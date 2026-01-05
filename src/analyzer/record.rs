use serde::{Deserialize, Serialize};
use std::{
    path::PathBuf,
    time::{Duration, Instant},
};

use super::chunk::ChunkId;

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub(crate) struct RecordData {
    pub project_info: ProjectAnalysisRecord,
    pub build_options: Vec<BuildOptionAnalysisRecord>,
    pub chunks: Vec<ChunkAnalysisRecord>,
    pub timing: TimingRecord,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub(crate) struct ProjectAnalysisRecord {
    pub project_dir: PathBuf,
    pub configure_path: PathBuf,
    pub source_files: Vec<PathBuf>,
    pub header_files: Vec<PathBuf>,
    pub automake_files: Vec<PathBuf>,
    pub built_files: Vec<PathBuf>,
    pub generated_files: Vec<PathBuf>,
    pub config_files: Vec<(PathBuf, PathBuf)>,
    pub subst_files: Vec<(PathBuf, PathBuf)>,
    pub total_commands: usize,
    pub total_chunks: usize,
    pub parameters: AnalysisParameters,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub(crate) struct AnalysisParameters {
    pub chunk_window_size: Option<usize>,
    pub disrespect_assignment: bool,
    pub type_inference_enabled: bool,
    pub build_option_analysis_enabled: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct BuildOptionAnalysisRecord {
    pub option_name: String,
    pub success: bool,
    pub failure_reason: Option<String>,
    pub llm_cost: Option<f64>,
    pub analysis_duration: Duration,
    pub value_candidates: Vec<String>,
    pub generated_features: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct ChunkAnalysisRecord {
    pub chunk_id: ChunkId,
    pub chunk_size: usize,
    pub translation_type: TranslationType,
    pub success: bool,
    pub failure_reason: Option<String>,
    pub llm_cost: Option<f64>,
    pub translation_duration: Duration,
    pub retry_count: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) enum TranslationType {
    Inlined,
    LLMAssisted,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct TimingRecord {
    pub total_duration_ms: u64,
    pub parse_duration_ms: u64,
    pub analysis_duration_ms: u64,
    pub build_option_duration_ms: u64,
    pub translation_duration_ms: u64,
    pub chunk_construction_duration_ms: u64,
    pub type_inference_duration_ms: u64,
}

impl Default for TimingRecord {
    fn default() -> Self {
        Self {
            total_duration_ms: 0,
            parse_duration_ms: 0,
            analysis_duration_ms: 0,
            build_option_duration_ms: 0,
            translation_duration_ms: 0,
            chunk_construction_duration_ms: 0,
            type_inference_duration_ms: 0,
        }
    }
}

#[derive(Debug, Default)]
pub(crate) struct RecordCollector {
    pub record_data: RecordData,
    timing_start: Option<Instant>,
    stage_start: Option<Instant>,
}

impl RecordCollector {
    pub(crate) fn new(
        project_dir: PathBuf,
        configure_path: PathBuf,
        parameters: AnalysisParameters,
    ) -> Self {
        Self {
            record_data: RecordData {
                project_info: ProjectAnalysisRecord {
                    project_dir,
                    configure_path,
                    parameters,
                    ..Default::default()
                },
                ..Default::default()
            },
            ..Default::default()
        }
    }

    pub(crate) fn start_timing(&mut self) {
        self.timing_start = Some(Instant::now());
    }

    pub(crate) fn start_stage(&mut self) {
        self.stage_start = Some(Instant::now());
    }

    pub(crate) fn end_stage_parse(&mut self) {
        if let Some(start) = self.stage_start.take() {
            self.record_data.timing.parse_duration_ms = start.elapsed().as_millis() as u64;
        }
    }

    pub(crate) fn end_stage_analysis(&mut self) {
        if let Some(start) = self.stage_start.take() {
            self.record_data.timing.analysis_duration_ms = start.elapsed().as_millis() as u64;
        }
    }

    pub(crate) fn end_stage_build_option(&mut self) {
        if let Some(start) = self.stage_start.take() {
            self.record_data.timing.build_option_duration_ms =
                start.elapsed().as_millis() as u64;
        }
    }

    pub(crate) fn end_stage_translation(&mut self) {
        if let Some(start) = self.stage_start.take() {
            self.record_data.timing.translation_duration_ms =
                start.elapsed().as_millis() as u64;
        }
    }

    pub(crate) fn end_stage_chunk_construction(&mut self) {
        if let Some(start) = self.stage_start.take() {
            self.record_data.timing.chunk_construction_duration_ms =
                start.elapsed().as_millis() as u64;
        }
    }

    pub(crate) fn end_stage_type_inference(&mut self) {
        if let Some(start) = self.stage_start.take() {
            self.record_data.timing.type_inference_duration_ms =
                start.elapsed().as_millis() as u64;
        }
    }

    pub(crate) fn finish_timing(&mut self) {
        if let Some(start) = self.timing_start.take() {
            self.record_data.timing.total_duration_ms = start.elapsed().as_millis() as u64;
        }
    }

    pub(crate) fn collect_project_info(
        &mut self,
        source_files: Vec<PathBuf>,
        header_files: Vec<PathBuf>,
        built_files: Vec<PathBuf>,
        generated_files: Vec<PathBuf>,
        config_files: Vec<(PathBuf, PathBuf)>,
        subst_files: Vec<(PathBuf, PathBuf)>,
        automake_files: Vec<PathBuf>,
        total_commands: usize,
        total_chunks: usize,
    ) {
        self.record_data.project_info.source_files = source_files;
        self.record_data.project_info.header_files = header_files;
        self.record_data.project_info.built_files = built_files;
        self.record_data.project_info.generated_files = generated_files;
        self.record_data.project_info.config_files = config_files;
        self.record_data.project_info.subst_files = subst_files;
        self.record_data.project_info.automake_files = automake_files;
        self.record_data.project_info.total_commands = total_commands;
        self.record_data.project_info.total_chunks = total_chunks;
    }

    pub(crate) fn add_build_option_record(
        &mut self,
        option_name: String,
        success: bool,
        failure_reason: Option<String>,
        llm_cost: Option<f64>,
        analysis_duration: Duration,
        value_candidates: Vec<String>,
        generated_features: Vec<String>,
    ) {
        self.record_data
            .build_options
            .push(BuildOptionAnalysisRecord {
                option_name,
                success,
                failure_reason,
                llm_cost,
                analysis_duration,
                value_candidates,
                generated_features,
            });
    }

    pub(crate) fn add_chunk_record(
        &mut self,
        chunk_id: ChunkId,
        chunk_size: usize,
        translation_type: TranslationType,
        success: bool,
        failure_reason: Option<String>,
        llm_cost: Option<f64>,
        translation_duration: Duration,
        retry_count: usize,
    ) {
        self.record_data.chunks.push(ChunkAnalysisRecord {
            chunk_id,
            chunk_size,
            translation_type,
            success,
            failure_reason,
            llm_cost,
            translation_duration,
            retry_count,
        });
    }

    pub(crate) fn export_json(&self, path: &std::path::Path) -> std::io::Result<()> {
        let json = serde_json::to_string_pretty(&self.record_data)?;
        std::fs::write(path, json)
    }

    pub(crate) fn export_build_options_csv(&self, path: &std::path::Path) -> std::io::Result<()> {
        let mut wtr = csv::Writer::from_path(path)?;

        // Write headers
        wtr.write_record(&[
            "option_name",
            "success",
            "failure_reason",
            "llm_cost",
            "analysis_duration_ms",
            "value_candidates",
            "generated_features",
        ])?;

        for record in &self.record_data.build_options {
            wtr.write_record(&[
                record.option_name.clone(),
                record.success.to_string(),
                record.failure_reason.clone().unwrap_or_default(),
                record.llm_cost.map_or_else(String::new, |c| c.to_string()),
                record.analysis_duration.as_millis().to_string(),
                record.value_candidates.join(";"),
                record.generated_features.join(";"),
            ])?;
        }

        wtr.flush()?;
        Ok(())
    }

    pub(crate) fn export_chunks_csv(&self, path: &std::path::Path) -> std::io::Result<()> {
        let mut wtr = csv::Writer::from_path(path)?;

        // Write headers
        wtr.write_record(&[
            "chunk_id",
            "chunk_size",
            "translation_type",
            "success",
            "failure_reason",
            "llm_cost",
            "translation_duration_ms",
            "retry_count",
        ])?;

        for record in &self.record_data.chunks {
            wtr.write_record(&[
                record.chunk_id.to_string(),
                record.chunk_size.to_string(),
                match record.translation_type {
                    TranslationType::Inlined => "Inlined".to_string(),
                    TranslationType::LLMAssisted => "LLM".to_string(),
                },
                record.success.to_string(),
                record.failure_reason.clone().unwrap_or_default(),
                record.llm_cost.map_or_else(String::new, |c| c.to_string()),
                record.translation_duration.as_millis().to_string(),
                record.retry_count.to_string(),
            ])?;
        }

        wtr.flush()?;
        Ok(())
    }
}
