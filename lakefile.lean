import Lake
open Lake DSL

package hansonToft where

@[default_target]
lean_lib HansonToft where
  roots := #[
    `HansonToft, `CycleCheck, `GraphLemmas,
    `BlockLemmas, `PathInsertion, `SimplePathExtension, `PathRecovery, `ColorRanks, `DeletionCorrespondence, `ColorDeletion, `RankedPaths, `RankInsertion, `InteriorFullPath, `EndpointFullPaths, `FullPathExtension, `RecoverableExtension, `EmbeddedPaths, `ConditionalPathLift, `TwoPathReduction, `CycleTripleLemma, `FiniteInjectionBound, `ChromaticLowerBound, `ChromaticUpperBound, `CycleEdgeDeletion, `ExceptionalCycleColoring, `CliquePaletteExtension, `AttachmentEdgeDeletion, `InternalEdgeDeletion, `EdgeCriticality, `FullCriticality, `CycleCountingBounds, `CliqueMissingColors,
    `CertificateK4, `CertificateK5, `CertificateK6,
    `CertificateK7, `CertificateK8, `CertificateK9
  ]
