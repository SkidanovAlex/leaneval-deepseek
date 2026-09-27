import Mathlib
import Submission.Work.Noncompact.proper_immersion_transverse
import Submission.Work.Noncompact.finite_preimages_and_discrete_doubleSet

/-!
# The non-compact case of Whitney's embedding theorem: compression of the domain

For a *non-compact* manifold `M` an immersion with isolated double points can be turned into an
*embedding* by a "compression of the domain": a smooth self-embedding `φ : M → M` whose image
omits one preimage of every double point (and, more strongly, whose image's closure avoids those
points).  The modified map `h ∘ φ` is then injective, and it is an embedding.

The construction of the compression itself (the "push the double points off to infinity" of the
classical proof: pairwise disjoint, locally finite tubes to infinity through the bad points) is
the content of the interface `Work.Noncompact.HasCompression`, proved elsewhere; this file
reduces the non-compact case of the target theorem to it.

The main point of the reduction is:

* `Work.Noncompact.exists_embedding_euclidean_of_compression`: a proper immersion in general
  position on a non-compact `n`-manifold (`n ≥ 2`) which admits a compression is an embedding.
-/

namespace Work.Noncompact

open scoped Manifold ContDiff
open Topology Filter

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The compression interface.**  For every closed discrete set `B` in a non-compact connected
smooth `n`-manifold (`n ≥ 2`) there is a smooth self-embedding `φ` whose image omits `B`, and
whose image's closure avoids `B` (i.e. each point of `B` is an interior point of the complement of
`φ '' univ`).

This is the geometric input of the non-compact case: `φ` is built by "pushing the points of `B`
off to infinity" along tubes; see `Submission/Work/Noncompact/NOTES_compression.md`. -/
def HasCompression (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] : Prop :=
  ∀ B : Set M, (∀ K : Set M, IsCompact K → (B ∩ K).Finite) →
    ∃ φ : M → M, ContMDiff (𝓡 n) (𝓡 n) ∞ φ ∧ IsEmbedding φ ∧
      (∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 n) φ x)) ∧
      B ∩ closure (Set.range φ) = ∅

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- **The non-compact case of Whitney's embedding theorem, reduced to the compression.** -/
theorem exists_embedding_euclidean_of_compression (hn : 2 ≤ n)
    [T2Space M] [SecondCountableTopology M] [Nonempty M] (hcomp : HasCompression n M) :
    ∃ e : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ e ∧ IsEmbedding e ∧
      (∀ x : M, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) e x)) := by
  classical
  have hn1 : 1 ≤ n := by omega
  obtain ⟨h, hsm, hprop, himm, htr⟩ :=
    exists_proper_immersion_transverse (n := n) (M := M) hn1
  obtain ⟨hfin, -, hlocfin⟩ := finite_preimages_and_discrete_doubleSet h hsm hprop himm htr
  -- ## the set of "kept" points: one point per value of `h`
  have hfib : ∀ y : EuclideanSpace ℝ (Fin (2 * n)), y ∈ Set.range h → (h ⁻¹' {y}).Nonempty := by
    rintro y ⟨x, hx⟩
    exact ⟨x, by rw [Set.mem_preimage, Set.mem_singleton_iff]; exact hx⟩
  let kept : EuclideanSpace ℝ (Fin (2 * n)) → M := fun y =>
    if hy : y ∈ Set.range h then Classical.choose (hfib y hy) else Classical.choice ‹Nonempty M›
  have hkept : ∀ y (hy : y ∈ Set.range h), h (kept y) = y := by
    intro y hy
    have hspec := Classical.choose_spec (hfib y hy)
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hspec
    simpa only [kept, dif_pos hy] using hspec
  let k : Set M := {x : M | ∃ y : EuclideanSpace ℝ (Fin (2 * n)), y ∈ Set.range h ∧ x = kept y}
  let B : Set M := kᶜ
  have h_inj_k : Set.InjOn h k := by
    rintro x ⟨y, hyr, rfl⟩ x' ⟨y', hy'r, rfl⟩ hxy
    have h1 := hkept y hyr
    have h2 := hkept y' hy'r
    rw [h1, h2] at hxy
    rw [hxy]
  have hB_sub : B ⊆ {x : M | ∃ y : M, y ≠ x ∧ h y = h x} := by
    intro x hx
    have hxk : x ∉ k := hx
    have hxr : h x ∈ Set.range h := ⟨x, rfl⟩
    have hk : kept (h x) ∈ k := ⟨h x, hxr, rfl⟩
    refine ⟨kept (h x), ?_, hkept (h x) hxr⟩
    intro hcon
    exact hxk (hcon ▸ hk)
  have hBfin : ∀ K : Set M, IsCompact K → (B ∩ K).Finite := by
    intro K hK
    exact (hlocfin K hK).subset (fun x hx => ⟨hB_sub hx.1, hx.2⟩)
  obtain ⟨φ, hφsm, hφemb, hφimm, hφB⟩ := hcomp B hBfin
  have hφk : Set.range φ ⊆ k := by
    intro x hx
    by_contra hcon
    have hmem : x ∈ B ∩ closure (Set.range φ) := ⟨hcon, subset_closure hx⟩
    rw [hφB] at hmem
    exact hmem
  -- ## the crux: no point of the image is a limit point of the image of the complement
  have hcrux : ∀ {U : Set M}, IsOpen U → ∀ {x : M}, x ∈ U →
      (h ∘ φ) x ∉ closure ((h ∘ φ) '' Uᶜ) := by
    intro U hUo x hxU hcl
    have hseq : ∀ m : ℕ, ∃ y : M, y ∉ U ∧ dist ((h ∘ φ) y) ((h ∘ φ) x) < (1:ℝ)/(m+1) := by
      intro m
      have hpos : (0:ℝ) < 1/(m+1) := by positivity
      have hgot := (Metric.mem_closure_iff.mp hcl) (1/(m+1)) hpos
      obtain ⟨z, hz, hdist⟩ := hgot
      obtain ⟨y, hyU, rfl⟩ := hz
      exact ⟨y, hyU, by rw [dist_comm]; exact hdist⟩
    choose y hyU hdist using hseq
    set S : Set M := h ⁻¹' Metric.closedBall ((h ∘ φ) x) 1 ∩ closure (φ '' Uᶜ) with hSdef
    have hKcpt : IsCompact (h ⁻¹' Metric.closedBall ((h ∘ φ) x) 1) :=
      hprop.isCompact_preimage (isCompact_closedBall _ _)
    have hScpt : IsCompact S := hKcpt.inter_right isClosed_closure
    have hmem : (h ∘ φ) x ∈ closure (h '' S) := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨m, hm⟩ := exists_nat_gt (1/ε)
      have hm' : (1:ℝ) < (m : ℝ) * ε := by
        rw [div_lt_iff₀ hε] at hm
        exact hm
      have hlt : (1:ℝ)/(m+1) < ε := by
        rw [div_lt_iff₀ (by positivity : (0:ℝ) < (m : ℝ) + 1)]
        nlinarith
      have hmnn : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
      have h2 : (1:ℝ)/(m+1) ≤ 1 :=
        div_le_one_of_le₀ (by linarith) (by positivity)
      refine ⟨(h ∘ φ) (y m), ⟨φ (y m), ⟨?_, ?_⟩, rfl⟩, ?_⟩
      · rw [Set.mem_preimage, Metric.mem_closedBall]
        have h1 : dist ((h ∘ φ) (y m)) ((h ∘ φ) x) ≤ 1 := by linarith [hdist m]
        simpa only [Function.comp_apply, dist_comm] using h1
      · exact subset_closure ⟨y m, hyU m, rfl⟩
      · rw [dist_comm]
        exact lt_trans (hdist m) hlt
    have hclosed : IsClosed (h '' S) := (hScpt.image hsm.continuous).isClosed
    rw [hclosed.closure_eq] at hmem
    obtain ⟨w, hwS, hwval⟩ := hmem
    obtain ⟨hwK, hwclos⟩ := hwS
    have hφxk : φ x ∈ k := hφk ⟨x, rfl⟩
    have hwval' : h w = h (φ x) := by simpa only [Function.comp_apply] using hwval
    have hne : w ≠ φ x := by
      intro hcon
      have hmem' : φ x ∈ closure (φ '' Uᶜ) := hcon ▸ hwclos
      have hcl' := hφemb.isInducing.closure_eq_preimage_closure_image (Uᶜ)
      have hxcl : x ∈ closure (Uᶜ) := by
        rw [hcl']
        exact hmem'
      rw [hUo.isClosed_compl.closure_eq] at hxcl
      exact hxcl hxU
    have hwk : w ∉ k := fun hwk => hne (h_inj_k hwk hφxk hwval')
    have hmem2 : w ∈ B ∩ closure (Set.range φ) :=
      ⟨hwk, closure_mono (Set.image_subset_range φ Uᶜ) hwclos⟩
    rw [hφB] at hmem2
    exact hmem2
  -- ## injectivity
  have he_inj : Function.Injective (h ∘ φ) := by
    intro x y hxy
    have hx := hφk ⟨x, rfl⟩
    have hy := hφk ⟨y, rfl⟩
    have : φ x = φ y := h_inj_k hx hy hxy
    exact hφemb.injective this
  -- ## the topology: `h ∘ φ` induces the topology of `M`
  have hnhds : ∀ x : M, 𝓝 x = comap (h ∘ φ) (𝓝 ((h ∘ φ) x)) := by
    intro x
    refine le_antisymm ?_ ?_
    · exact ((hsm.comp hφsm).continuous.continuousAt (x := x)).le_comap
    · intro U hU
      obtain ⟨U', hU'sub, hU'open, hxU'⟩ := mem_nhds_iff.mp hU
      have hVopen : IsOpen ((closure ((h ∘ φ) '' (U')ᶜ))ᶜ) := isClosed_closure.isOpen_compl
      have hxV : (h ∘ φ) x ∈ ((closure ((h ∘ φ) '' (U')ᶜ))ᶜ) := hcrux hU'open hxU'
      have hVnhds : ((closure ((h ∘ φ) '' (U')ᶜ))ᶜ) ∈ 𝓝 ((h ∘ φ) x) :=
        hVopen.mem_nhds hxV
      have hsub : (h ∘ φ) ⁻¹' ((closure ((h ∘ φ) '' (U')ᶜ))ᶜ) ⊆ U := by
        intro z hz
        by_contra hzU
        have hz' : z ∈ (U')ᶜ := fun hcon => hzU (hU'sub hcon)
        have hmem : (h ∘ φ) z ∈ closure ((h ∘ φ) '' (U')ᶜ) := subset_closure ⟨z, hz', rfl⟩
        exact hz hmem
      exact mem_comap.mpr ⟨_, hVnhds, hsub⟩
  refine ⟨h ∘ φ, ?_, ?_, ?_⟩
  · exact hsm.comp hφsm
  · exact (isEmbedding_iff (h ∘ φ)).mpr ⟨isInducing_iff_nhds.mpr hnhds, he_inj⟩
  · intro x
    have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
    have hcomp : mfderiv (𝓡 n) (𝓡 (2 * n)) (h ∘ φ) x
        = (mfderiv (𝓡 n) (𝓡 (2 * n)) h (φ x)).comp (mfderiv (𝓡 n) (𝓡 n) φ x) :=
      mfderiv_comp x (hsm.mdifferentiableAt hne) (hφsm.mdifferentiableAt hne)
    rw [hcomp]
    intro a b hab
    exact hφimm x (himm (φ x) hab)

end Work.Noncompact
