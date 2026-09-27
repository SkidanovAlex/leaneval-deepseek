import Mathlib
import Submission.Work.Noncompact.CompressionTube.Defs
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.exists_collar_twosided
import Submission.Work.Noncompact.CompressionTube.exists_shrunk_tube
import Submission.Work.Noncompact.CompressionTube.isLocalDiffeomorph_of_immersion

/-!
# The compression tube: copies of the proved declarations from `exists_compression_tube`

`Submission/Work/Noncompact/CompressionTube/exists_compression_tube.lean` contains a `sorry`, so the
glue of the non-compact case cannot import it.  The declarations below are copies (with the `_drive`
suffix) of the *proved* parts of that file: the collar-to-tube compression (`tube_of_collar_drive`),
the tube inside an open set along a line (`exists_tube_in_open_drive`), the line input
(`LineInput_drive`) and the assembly from the lines (`exists_compressionTube_of_lines_drive`).
-/

universe u v

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.Noncompact.CompressionTube

open scoped Manifold ContDiff
open Topology Set Function

noncomputable section

variable {M : Type*} [TopologicalSpace M]

theorem tube_of_collar_drive {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M] [ConnectedSpace M]
    {γ : ℝ → M} {Ψ₀ : EuclideanSpace ℝ (Fin (n - 1)) × ℝ → M}
    (hsm : ContMDiff (MCprod n) (MC n) smoothOrder Ψ₀)
    (hcore : ∀ s : ℝ, Ψ₀ ((0 : EuclideanSpace ℝ (Fin (n - 1))), s) = γ s)
    (hinj : Set.InjOn Ψ₀ {p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ | ‖p.1‖ ≤ 1})
    (himm : ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, ‖p.1‖ ≤ 1 →
      Function.Injective (mfderiv (MCprod n) (MC n) Ψ₀ p))
    (hesc : ∀ K : Set M, IsCompact K → ∃ S : ℝ,
      ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, ‖p.1‖ ≤ 1 → S ≤ |p.2| → Ψ₀ p ∉ K) :
    ∃ Ψ : EuclideanSpace ℝ (Fin (n - 1)) × ℝ → M,
      ContMDiff (MCprod n) (MC n) smoothOrder Ψ ∧ Topology.IsEmbedding Ψ ∧
      (∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ,
        Function.Injective (mfderiv (MCprod n) (MC n) Ψ p)) ∧
      (∀ s : ℝ, Ψ ((0 : EuclideanSpace ℝ (Fin (n - 1))), s) = γ s) ∧
      (∀ K : Set M, IsCompact K → ∃ S : ℝ,
        ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, ‖p.1‖ ≤ 1 → S ≤ |p.2| → Ψ p ∉ K) := by
  classical
  set ρ : ℝ → ℝ := fun _ => (1 : ℝ) / 2 with hρdef
  have hρcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ := contDiff_const
  have hρpos : ∀ s : ℝ, 0 < ρ s := fun s => by norm_num [hρdef]
  have hρle : ∀ s : ℝ, ρ s ≤ 1 := fun s => by norm_num [hρdef]
  have hsm' : ContMDiff (MCprod n) (MC n) smoothOrder (fun p => Ψ₀ (shrink n ρ p)) :=
    hsm.comp (shrink_contMDiff n hρcd)
  have hnorm : ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, ‖(shrink n ρ p).1‖ ≤ 1 := fun p =>
    le_of_lt (lt_of_lt_of_le (shrink_fst_norm_lt n hρpos p) (hρle p.2))
  have himm' : ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ,
      Function.Injective (mfderiv (MCprod n) (MC n) (fun p => Ψ₀ (shrink n ρ p)) p) := by
    intro p
    have h1 : MDifferentiableAt (MCprod n) (MCprod n) (shrink n ρ) p :=
      (shrink_contMDiff n hρcd).contMDiffAt.mdifferentiableAt (by simp [smoothOrder])
    have h2 : MDifferentiableAt (MCprod n) (MC n) Ψ₀ (shrink n ρ p) :=
      hsm.contMDiffAt.mdifferentiableAt (by simp [smoothOrder])
    change Function.Injective (mfderiv (MCprod n) (MC n) (Ψ₀ ∘ shrink n ρ) p)
    rw [mfderiv_comp (I := MCprod n) (I' := MCprod n) (I'' := MC n) (x := p)
      (f := shrink n ρ) (g := Ψ₀) h2 h1]
    intro v w hvw
    exact shrink_mfderiv_injective n hρcd hρpos p (himm (shrink n ρ p) (hnorm p) hvw)
  have hinj' : Function.Injective (fun p => Ψ₀ (shrink n ρ p)) := by
    intro p q hpq
    exact shrink_injective n hρpos (hinj (hnorm p) (hnorm q) hpq)
  refine ⟨fun p => Ψ₀ (shrink n ρ p), hsm', ?_, himm', ?_, ?_⟩
  · have hld : IsLocalDiffeomorph (MCprod n) (MC n) smoothOrder
        (fun p => Ψ₀ (shrink n ρ p)) := by
      rw [← chartedSpaceSelf_prod] at hsm' himm' ⊢
      exact isLocalDiffeomorph_of_immersion (n := n) (by omega) hsm' himm'
    exact ((hld.isLocalHomeomorph).isOpenEmbedding_of_injective hinj').toIsEmbedding
  · intro s
    show Ψ₀ (shrink n ρ ((0 : EuclideanSpace ℝ (Fin (n - 1))), s)) = γ s
    rw [shrink_core n ρ s]
    exact hcore s
  · intro K hK
    obtain ⟨S, hS⟩ := hesc K hK
    refine ⟨S, ?_⟩
    intro p hp hSp
    exact hS (shrink n ρ p) (hnorm p) (by rw [shrink_snd]; exact hSp)

/-- **A tube inside a prescribed open set along a given proper line.**  The two-sided collar of the
line, compressed radially in the transverse direction, is a global tube; shrinking it further
(`exists_shrunk_tube`) puts its image inside the open set `U`, while keeping the line as its
core. -/
theorem exists_tube_in_open_drive {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M] [ConnectedSpace M]
    {γ : ℝ → M} {U : Set M} (hUo : IsOpen U) (hU : Set.range γ ⊆ U)
    (hγ : ContMDiff MCreal (MC n) smoothOrder γ) (hinj : Function.Injective γ)
    (hprop : IsProperMap γ) (himm : ∀ s : ℝ, Function.Injective (mfderiv MCreal (MC n) γ s)) :
    ∃ T : EuclideanSpace ℝ (Fin (n - 1)) × ℝ → M,
      ContMDiff (MCprod n) (MC n) smoothOrder T ∧ Topology.IsEmbedding T ∧
      (∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ,
        Function.Injective (mfderiv (MCprod n) (MC n) T p)) ∧
      (∀ s : ℝ, T ((0 : EuclideanSpace ℝ (Fin (n - 1))), s) = γ s) ∧
      (∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, T p ∈ U) ∧
      (∀ K : Set M, IsCompact K → ∃ S : ℝ,
        ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, ‖p.1‖ ≤ 1 → S ≤ |p.2| → T p ∉ K) := by
  obtain ⟨Ψ₀, hsm, hcore, hinj₀, himm₀, hesc₀⟩ :=
    exists_collar_twosided (n := n) hn hγ hinj hprop himm
  obtain ⟨Ψ, hΨsm, hΨemb, hΨimm, hΨcore, hΨesc⟩ :=
    tube_of_collar_drive (n := n) hn hsm hcore hinj₀ himm₀ hesc₀
  obtain ⟨T, hTsm, hTemb, hTimm, hTcore, hTsub, -, hTesc⟩ :=
    exists_shrunk_tube (n := n) hn (γ := γ) (Ψ := Ψ) hΨsm hΨemb hΨimm hΨcore hΨesc
      (C := (∅ : Set M)) isClosed_empty (Set.disjoint_empty _) (U := U) hUo hU
  exact ⟨T, hTsm, hTemb, hTimm, hTcore, hTsub, hTesc⟩

/-! ### The assembly from the lines -/

def LineInput_drive (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M] {B : Set M} (W : B → Set M) : Prop :=
  ∀ b : B, ∃ γ : ℝ → M, γ 1 = (b : M) ∧ ContMDiff MCreal (MC n) smoothOrder γ ∧
    Function.Injective γ ∧ IsProperMap γ ∧
    (∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) γ t)) ∧ Set.range γ ⊆ W b

theorem exists_compressionTube_of_lines_drive {n : ℕ} (hn : 2 ≤ n) {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [ConnectedSpace M]
    {B : Set M} {W : B → Set M} (hWo : ∀ b, IsOpen (W b))
    (hWdisj : ∀ b b', b ≠ b' → Disjoint (W b) (W b'))
    (hWfin : ∀ K : Set M, IsCompact K → {b : B | (W b ∩ K).Nonempty}.Finite)
    (hL : LineInput_drive n M W) (ι : Type v) (e : B ≃ ι) :
    Nonempty (Work.Noncompact.CompressionTube.{u, v} n M B) := by
  classical
  choose γ hγ1 hγsm hγinj hγprop hγimm hγsub using hL
  -- ## the tubes, shrunk into the canals
  have htube : ∀ b : B, ∃ T : EuclideanSpace ℝ (Fin (n - 1)) × ℝ → M,
      ContMDiff (MCprod n) (MC n) smoothOrder T ∧ Topology.IsEmbedding T ∧
      (∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ,
        Function.Injective (mfderiv (MCprod n) (MC n) T p)) ∧
      T ((0 : EuclideanSpace ℝ (Fin (n - 1))), 1) = (b : M) ∧
      (∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, T p ∈ W b) ∧
      (∀ K' : Set M, IsCompact K' → ∃ S : ℝ,
        ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, ‖p.1‖ ≤ 1 → S ≤ |p.2| → T p ∉ K') := by
    intro b
    obtain ⟨T, hTsm, hTemb, hTimm, hTcore, hTsub, hTesc⟩ :=
      exists_tube_in_open_drive (n := n) hn (hWo b) (hγsub b) (hγsm b) (hγinj b) (hγprop b) (hγimm b)
    exact ⟨T, hTsm, hTemb, hTimm, by rw [hTcore 1, hγ1 b], hTsub, hTesc⟩
  choose T hTsm hTemb hTimm hT1 hTsub hTesc using htube
  have hTdisj : ∀ b b' : B, b ≠ b' →
      Disjoint (Set.range (T b)) (Set.range (T b')) :=
    fun b b' hbb' => (hWdisj b b' hbb').mono (Set.range_subset_iff.mpr (hTsub b))
      (Set.range_subset_iff.mpr (hTsub b'))
  have hTfin : ∀ K : Set M, IsCompact K →
      {b : B | ∃ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, ‖p.1‖ ≤ 1 ∧ T b p ∈ K}.Finite := by
    intro K hK
    refine (hWfin K hK).subset ?_
    rintro b ⟨p, -, hpK⟩
    exact ⟨T b p, hTsub b p, hpK⟩
  -- ## the tube datum, indexed by `ι`
  refine ⟨{ ι := ι, tube := fun i => T (e.symm i), contMDiff_tube := ?_, isEmbedding_tube := fun i => hTemb (e.symm i), immersion_tube := ?_, covers := ?_, escapes := fun i K' hK' => hTesc (e.symm i) K' hK', disjoint := ?_, locallyFinite := ?_ }⟩
  · intro i
    rw [chartedSpaceSelf_prod]
    exact hTsm (e.symm i)
  · intro i p
    rw [chartedSpaceSelf_prod]
    exact hTimm (e.symm i) p
  · intro y hy
    refine Set.mem_iUnion.mpr ⟨e ⟨y, hy⟩, ?_⟩
    refine ⟨((0 : EuclideanSpace ℝ (Fin (n - 1))), 1), ⟨rfl, by norm_num⟩, ?_⟩
    show T (e.symm (e ⟨y, hy⟩)) ((0 : EuclideanSpace ℝ (Fin (n - 1))), 1) = y
    rw [Equiv.symm_apply_apply, hT1]
  · intro i j hij
    have hne : e.symm i ≠ e.symm j := by
      intro h
      exact hij (by rw [← Equiv.apply_symm_apply e i, h, Equiv.apply_symm_apply e j])
    exact hTdisj (e.symm i) (e.symm j) hne
  · intro K' hK'
    have hEq : {i : ι | ∃ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ,
          ‖p.1‖ ≤ 1 ∧ T (e.symm i) p ∈ K'}
        = e '' {b : B | ∃ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ,
          ‖p.1‖ ≤ 1 ∧ T b p ∈ K'} := by
      ext i
      constructor
      · rintro ⟨p, hp, hmem⟩
        exact ⟨e.symm i, ⟨p, hp, hmem⟩, Equiv.apply_symm_apply e i⟩
      · rintro ⟨b, ⟨p, hp, hmem⟩, rfl⟩
        exact ⟨p, hp, by rw [Equiv.symm_apply_apply]; exact hmem⟩
    rw [hEq]
    exact (hTfin K' hK').image e


end

end Work.Noncompact.CompressionTube
