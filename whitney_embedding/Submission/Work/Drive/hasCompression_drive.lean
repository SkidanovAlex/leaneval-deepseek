import Mathlib
import Submission.Work.Noncompact.Compression
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.SpineDefs
import Submission.Work.Noncompact.Routing.exists_canals
import Submission.Work.Noncompact.CompressionTube.fromTube
import Submission.Work.Drive.Rays.lineOfTwoRays_drive
import Submission.Work.Drive.Rays.lineOfProperRay
import Submission.Work.Drive.ray_by_truncation
import Submission.Work.Drive.tube_drive

/-!
# The compression of the domain, driven from the spine arcs

`Work.Drive.hasCompression_drive` is the non-compact half of Whitney's strong embedding theorem, in
the same form as `Work.Noncompact.hasCompression` but with the missing line input built directly
from the *spine arcs* of `Work.Noncompact.CompressionTube.exists_nested_canals`:

for every `b : B` the arcs `γ b i` (`i ≥ lev b`) join up (`ends`) into a single continuous path
`ρ : ℝ → M` (constant `b` on `ℝ≤0`), which stays in the canal `W b` (the arcs from level `i` on lie
in `D b i ⊆ W b`) and escapes every compact set (a compact set lies in some level `K N`, and the
arcs at level `≥ N` avoid `K N`).  Feeding `ρ` to `Work.Drive.line_of_escaping_path` gives the line
of `LineInput_drive`, and the assembly `exists_compressionTube_of_lines_drive` (copied from the
proved part of `exists_compression_tube`) finishes the job.
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Set Filter Topology
open scoped Topology

noncomputable section

/-! ### Gluing a `ℤ`-indexed chain of arcs into a continuous path -/

/-- The concatenation of the arcs `ar k` on their own unit intervals: at time `t` it evaluates the
arc of index `⌊t⌋` at the fractional part of `t`. -/
def glueMap {M : Type*} (ar : ℤ → ℝ → M) (t : ℝ) : M := ar ⌊t⌋ (Int.fract t)

/-- On the closed unit interval `Icc k (k+1)` the concatenation is a single arc, reparametrised. -/
theorem glueMap_eq_on_Icc {M : Type*} {ar : ℤ → ℝ → M}
    (hglue : ∀ k : ℤ, ar k 1 = ar (k+1) 0) (k : ℤ) :
    ∀ s ∈ Set.Icc (k:ℝ) ((k:ℝ)+1), glueMap ar s = ar k (s - (k:ℝ)) := by
  intro s hs
  rcases lt_or_eq_of_le hs.2 with hlt | heq
  · have hfl : ⌊s⌋ = k := Int.floor_eq_iff.mpr ⟨hs.1, hlt⟩
    rw [glueMap, hfl]
    congr 1
    rw [Int.fract, hfl]
  · subst heq
    rw [glueMap, show ((k:ℝ)+1) = ((k+1 : ℤ) : ℝ) by push_cast; ring, Int.floor_intCast,
      Int.fract_intCast, (hglue k).symm]
    congr 1
    push_cast
    ring

/-- The concatenation is continuous on every closed unit interval. -/
theorem continuousOn_glueMap {M : Type*} [TopologicalSpace M] {ar : ℤ → ℝ → M}
    (hcont : ∀ k, Continuous (ar k)) (hglue : ∀ k, ar k 1 = ar (k+1) 0) (k : ℤ) :
    ContinuousOn (glueMap ar) (Set.Icc (k:ℝ) ((k:ℝ)+1)) := by
  have hc : Continuous (fun s : ℝ => ar k (s - (k:ℝ))) :=
    (hcont k).comp (continuous_id.sub continuous_const)
  exact hc.continuousOn.congr (glueMap_eq_on_Icc hglue k)

/-- **The concatenation of a matching `ℤ`-indexed chain of arcs is continuous.** -/
theorem continuous_glueMap {M : Type*} [TopologicalSpace M] {ar : ℤ → ℝ → M}
    (hcont : ∀ k, Continuous (ar k)) (hglue : ∀ k, ar k 1 = ar (k+1) 0) :
    Continuous (glueMap ar) := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases hint : ∃ n : ℤ, t = (n : ℝ)
  · obtain ⟨n, rfl⟩ := hint
    have hmem : Set.Ioo ((n:ℝ) - 1) ((n:ℝ) + 1) ∈ nhds (n:ℝ) :=
      isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    rw [continuousAt_iff_continuous_left_right]
    constructor
    · have hIcc : ContinuousWithinAt (glueMap ar)
          (Set.Icc (((n-1:ℤ):ℝ)) (((n-1:ℤ):ℝ)+1)) (n:ℝ) :=
        (continuousOn_glueMap hcont hglue (n-1)).continuousWithinAt (by
          constructor <;> push_cast <;> linarith)
      have hsub : Set.Iio (n:ℝ) ∩ Set.Ioo ((n:ℝ)-1) ((n:ℝ)+1) ⊆
          Set.Icc (((n-1:ℤ):ℝ)) (((n-1:ℤ):ℝ)+1) := by
        rintro x hx
        simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioo] at hx
        obtain ⟨hx1, hx2, hx3⟩ := hx
        constructor <;> push_cast <;> linarith
      exact continuousWithinAt_Iio_iff_Iic.mp ((continuousWithinAt_inter hmem).mp (hIcc.mono hsub))
    · have hIcc : ContinuousWithinAt (glueMap ar)
          (Set.Icc (n:ℝ) ((n:ℝ)+1)) (n:ℝ) :=
        (continuousOn_glueMap hcont hglue n).continuousWithinAt (by
          constructor <;> push_cast <;> linarith)
      have hsub : Set.Ioi (n:ℝ) ∩ Set.Ioo ((n:ℝ)-1) ((n:ℝ)+1) ⊆
          Set.Icc (n:ℝ) ((n:ℝ)+1) := by
        rintro x hx
        simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioo] at hx
        obtain ⟨hx1, hx2, hx3⟩ := hx
        exact ⟨le_of_lt hx1, le_of_lt hx3⟩
      exact continuousWithinAt_Ioi_iff_Ici.mp ((continuousWithinAt_inter hmem).mp (hIcc.mono hsub))
  · push Not at hint
    have hle : (⌊t⌋ : ℝ) ≤ t := Int.floor_le t
    have hne : t ≠ (⌊t⌋ : ℝ) := hint ⌊t⌋
    have hlt : (⌊t⌋:ℝ) < t := lt_of_le_of_ne hle (Ne.symm hne)
    have hlt2 : t < (⌊t⌋:ℝ) + 1 := Int.lt_floor_add_one t
    have hopen : Set.Ioo (⌊t⌋:ℝ) ((⌊t⌋:ℝ)+1) ∈ nhds t := isOpen_Ioo.mem_nhds ⟨hlt, hlt2⟩
    refine (ContinuousWithinAt.continuousAt ?_ hopen)
    exact ((continuousOn_glueMap hcont hglue ⌊t⌋).continuousWithinAt
      ⟨le_of_lt hlt, le_of_lt hlt2⟩).mono (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)

/-! ### Extending a sequence of arcs to a `ℤ`-indexed family -/

/-- A sequence of arcs, extended by the constant map `b` on the negative indices. -/
def extendedArcs {M : Type*} (σ : ℕ → ℝ → M) (b : M) : ℤ → ℝ → M :=
  fun k => if 0 ≤ k then σ k.toNat else fun _ => b

theorem extendedArcs_of_nonneg {M : Type*} (σ : ℕ → ℝ → M) (b : M) {k : ℤ} (hk : 0 ≤ k) :
    extendedArcs σ b k = σ k.toNat := if_pos hk

theorem extendedArcs_of_neg {M : Type*} (σ : ℕ → ℝ → M) (b : M) {k : ℤ} (hk : ¬ 0 ≤ k) :
    extendedArcs σ b k = fun _ => b := if_neg hk

theorem extendedArcs_continuous {M : Type*} [TopologicalSpace M] {σ : ℕ → ℝ → M}
    (hσ : ∀ m, Continuous (σ m)) (b : M) : ∀ k, Continuous (extendedArcs σ b k) := by
  intro k
  by_cases hk : 0 ≤ k
  · rw [extendedArcs_of_nonneg _ _ hk]; exact hσ k.toNat
  · rw [extendedArcs_of_neg _ _ hk]; exact continuous_const

theorem toNat_succ_eq (k : ℤ) (hk : 0 ≤ k) : (k+1).toNat = k.toNat + 1 := by
  have h1 : ((k+1).toNat : ℤ) = k + 1 := Int.toNat_of_nonneg (by omega)
  have h2 : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
  omega

/-- The extended arcs match at consecutive integer times for a matching sequence. -/
theorem extendedArcs_glue {M : Type*} {σ : ℕ → ℝ → M} {b : M} (h0 : σ 0 0 = b)
    (h1 : ∀ m, σ m 1 = σ (m+1) 0) :
    ∀ k : ℤ, extendedArcs σ b k 1 = extendedArcs σ b (k+1) 0 := by
  intro k
  by_cases hk : 0 ≤ k
  · have hk1 : 0 ≤ k + 1 := by omega
    rw [extendedArcs_of_nonneg _ _ hk, extendedArcs_of_nonneg _ _ hk1, toNat_succ_eq k hk]
    exact h1 k.toNat
  · by_cases hk1 : 0 ≤ k + 1
    · have hkneg : k = -1 := by omega
      rw [extendedArcs_of_neg _ _ hk, extendedArcs_of_nonneg _ _ hk1, hkneg]
      exact h0.symm
    · rw [extendedArcs_of_neg _ _ hk, extendedArcs_of_neg _ _ hk1]

/-! ### The escaping path of a spine -/

/-- **The escaping path of the spine of a strand.**  The arcs `γ b i` (`i ≥ lev b`) of a
`SpineData` concatenate into a continuous path `ρ : ℝ → M` with `ρ 0 = b`, staying in `W b` for
`t ≥ 0` and escaping every compact set. -/
theorem exists_escapingPath_of_spine {M : Type*} [TopologicalSpace M]
    {B : Set M} {K : ℕ → Set M} {W : B → Set M} {lev : B → ℕ} {q : B → ℕ → M}
    {γ : B → ℕ → ℝ → M}
    (hKsub : ∀ i, K i ⊆ interior (K (i + 1)))
    (hKuniv : (⋃ i, K i) = (Set.univ : Set M))
    (hspine : Work.Noncompact.CompressionTube.SpineData K B lev q γ)
    (htailW : ∀ (b : B) (i : ℕ), lev b ≤ i →
      (⋃ j : {j : ℕ // i ≤ j}, γ b (j : ℕ) '' Set.Icc (0:ℝ) 1) ⊆ W b)
    (hqlev : ∀ b : B, q b (lev b) = (b : M)) (b : B) :
    ∃ ρ : ℝ → M, Continuous ρ ∧ ρ 0 = (b : M) ∧ (∀ t : ℝ, 0 ≤ t → ρ t ∈ W b) ∧
      (∀ K' : Set M, IsCompact K' → ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ρ t ∉ K') := by
  classical
  set σ : ℕ → ℝ → M := fun m => γ b (lev b + m) with hσdef
  have hσcont : ∀ m, Continuous (σ m) := fun m =>
    hspine.cont b (lev b + m) (Nat.le_add_right _ _)
  have hσ0 : ∀ m, σ m 0 = q b (lev b + m) := fun m =>
    (hspine.ends b (lev b + m) (Nat.le_add_right _ _)).1
  have hσ1 : ∀ m, σ m 1 = q b (lev b + m + 1) := fun m =>
    (hspine.ends b (lev b + m) (Nat.le_add_right _ _)).2
  have hσglue : ∀ m : ℕ, σ m 1 = σ (m + 1) 0 := by
    intro m
    rw [hσ1 m, hσ0 (m + 1)]
    congr 1
  have hσ0b : σ 0 0 = (b : M) := by rw [hσ0 0, Nat.add_zero, hqlev b]
  have hval : ∀ t : ℝ, 0 ≤ t → glueMap (extendedArcs σ (b : M)) t = σ ⌊t⌋.toNat (Int.fract t) := by
    intro t ht
    rw [glueMap, extendedArcs_of_nonneg _ _ (Int.le_floor.mpr (by exact_mod_cast ht))]
  refine ⟨glueMap (extendedArcs σ (b : M)), ?_, ?_, ?_, ?_⟩
  · exact continuous_glueMap (extendedArcs_continuous hσcont (b : M))
      (extendedArcs_glue hσ0b hσglue)
  · rw [glueMap, Int.floor_zero, Int.fract_zero,
      extendedArcs_of_nonneg _ _ (le_refl (0 : ℤ))]
    exact hσ0b
  · intro t ht
    have hσeq : σ ⌊t⌋.toNat (Int.fract t) = γ b (lev b + ⌊t⌋.toNat) (Int.fract t) := rfl
    rw [hval t ht, hσeq]
    refine htailW b (lev b) le_rfl (Set.mem_iUnion.mpr ?_)
    refine ⟨⟨lev b + ⌊t⌋.toNat, ?_⟩, ?_⟩
    · exact Nat.le_add_right _ _
    · exact ⟨Int.fract t, ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩, rfl⟩
  · intro K' hK'
    obtain ⟨N, hN⟩ : ∃ N : ℕ, K' ⊆ K N := by
      have hcov : K' ⊆ ⋃ i, interior (K (i + 1)) := by
        intro x hx
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hKuniv ▸ Set.mem_univ x)
        exact Set.mem_iUnion.mpr ⟨i, hKsub i hi⟩
      obtain ⟨s, hs⟩ := hK'.elim_finite_subcover (fun i : ℕ => interior (K (i + 1)))
        (fun i => isOpen_interior) hcov
      refine ⟨s.sup (fun i => i + 1), fun x hx => ?_⟩
      obtain ⟨i, his, hxi⟩ := Set.mem_iUnion₂.mp (hs hx)
      exact (Work.Noncompact.CompressionTube.monotone_K K hKsub (Finset.le_sup his))
        (interior_subset hxi)
    refine ⟨(N : ℝ), fun t ht hmem => ?_⟩
    have hNt : (N : ℤ) ≤ ⌊t⌋ := Int.le_floor.mpr (by exact_mod_cast ht)
    have h0t : (0 : ℤ) ≤ ⌊t⌋ := le_trans (by positivity) hNt
    have htoNat : N ≤ ⌊t⌋.toNat := (Int.le_toNat h0t).mpr hNt
    have hσeq : σ ⌊t⌋.toNat (Int.fract t) = γ b (lev b + ⌊t⌋.toNat) (Int.fract t) := rfl
    have himg : σ ⌊t⌋.toNat (Int.fract t) ∈ γ b (lev b + ⌊t⌋.toNat) '' Set.Icc (0:ℝ) 1 := by
      rw [hσeq]
      exact ⟨Int.fract t, ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩, rfl⟩
    rw [hval t (le_trans (Nat.cast_nonneg N) ht)] at hmem
    have hKi := Set.disjoint_left.mp
      (hspine.disjoint_K b (lev b + ⌊t⌋.toNat) (Nat.le_add_right _ _)) himg
    exact hKi (Work.Noncompact.CompressionTube.monotone_K K hKsub
      (le_trans htoNat (Nat.le_add_left _ _)) (hN hmem))

/-! ### The line input, from the escaping path -/

/-- **The line input inside the canals.**  The escaping paths of `exists_escapingPath_of_spine`,
fed to `Work.Drive.line_of_escaping_path`, give the smooth proper embedded immersive lines of the
tube assembly. -/
theorem lineInput_of_spine {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {B : Set M} {W : B → Set M} {K : ℕ → Set M} {lev : B → ℕ} {q : B → ℕ → M}
    {γ : B → ℕ → ℝ → M}
    (hWo : ∀ b, IsOpen (W b))
    (hKsub : ∀ i, K i ⊆ interior (K (i + 1)))
    (hKuniv : (⋃ i, K i) = (Set.univ : Set M))
    (hspine : Work.Noncompact.CompressionTube.SpineData K B lev q γ)
    (htailW : ∀ (b : B) (i : ℕ), lev b ≤ i →
      (⋃ j : {j : ℕ // i ≤ j}, γ b (j : ℕ) '' Set.Icc (0:ℝ) 1) ⊆ W b)
    (hqlev : ∀ b : B, q b (lev b) = (b : M)) :
    Work.Noncompact.CompressionTube.LineInput_drive n M W := by
  intro b
  obtain ⟨ρ, hρc, hρ0, hρW, hρesc⟩ :=
    exists_escapingPath_of_spine hKsub hKuniv hspine htailW hqlev b
  -- the escaping ray (`ray_by_truncation`, the lead's ray design) and the hairpin
  obtain ⟨r, hr0, hrsm, hrinj, hrp, hrimm, hrW⟩ :=
    ray_by_truncation (n := n) hn (hWo b) hρc hρW hρesc
  obtain ⟨γ', hγ1, hγsm, hγinj, hγprop, hγimm, hγsub⟩ :=
    Work.Drive.Rays.lineOfProperRay (n := n) hn (hWo b) hrsm hrinj hrp hrimm hrW
  exact ⟨γ', by rw [hγ1, hr0, hρ0], hγsm, hγinj, hγprop, hγimm, hγsub⟩

/-! ### The line input from two rays at each base point -/

/-- **The two-rays datum at a point.**  Two escaping rays from `b` inside `W`, meeting only at `b`,
with the two halves of one straight chart line as their germs at `b`. -/
def TwoRaysAt {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M] (W : Set M) (b : M) : Prop :=
  ∃ (r r' : ℝ → M) (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (w : EuclideanSpace ℝ (Fin n)) (e : ℝ),
    r 0 = b ∧ r' 0 = b ∧ 0 < e ∧ w ≠ 0 ∧
    c ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M ∧ b ∈ c.source ∧
    ContMDiffOn Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder r (Set.Ici (0:ℝ)) ∧
    ContMDiffOn Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder r' (Set.Ici (0:ℝ)) ∧
    Set.InjOn r (Set.Ici (0:ℝ)) ∧ Set.InjOn r' (Set.Ici (0:ℝ)) ∧
    IsProperMap (fun t : Set.Ici (0:ℝ) => r t) ∧
    IsProperMap (fun t : Set.Ici (0:ℝ) => r' t) ∧
    (∀ t : ℝ, 0 ≤ t → Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n) r t)) ∧
    (∀ t : ℝ, 0 ≤ t → Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n) r' t)) ∧
    (∀ t : ℝ, 0 ≤ t → r t ∈ W) ∧ (∀ t : ℝ, 0 ≤ t → r' t ∈ W) ∧
    (∀ x : M, x ∈ r '' Set.Ici (0:ℝ) → x ∈ r' '' Set.Ici (0:ℝ) → x = b) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ e → r t = c.symm (c b + t • w)) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ e → r' t = c.symm (c b + t • (-w)))

/-- **The line input from the two-rays datum.**  The escaping path of `exists_escapingPath_of_spine`
at `b`, the two rays at its base point and the germ gluing
`line_of_two_germed_oneSided_rays_drive` give the smooth proper embedded immersive line of
`LineInput_drive`. -/
theorem lineInput_of_twoRays {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {B : Set M} {W : B → Set M} {K : ℕ → Set M} {lev : B → ℕ} {q : B → ℕ → M}
    {γ : B → ℕ → ℝ → M}
    (hKsub : ∀ i, K i ⊆ interior (K (i + 1)))
    (hKuniv : (⋃ i, K i) = (Set.univ : Set M))
    (hspine : Work.Noncompact.CompressionTube.SpineData K B lev q γ)
    (htailW : ∀ (b : B) (i : ℕ), lev b ≤ i →
      (⋃ j : {j : ℕ // i ≤ j}, γ b (j : ℕ) '' Set.Icc (0:ℝ) 1) ⊆ W b)
    (hqlev : ∀ b : B, q b (lev b) = (b : M))
    (htwo : ∀ (b : B) (ρ : ℝ → M), Continuous ρ → (∀ t : ℝ, 0 ≤ t → ρ t ∈ W b) →
      (∀ K' : Set M, IsCompact K' → ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ρ t ∉ K') →
      TwoRaysAt (n := n) (W b) (ρ 0)) :
    Work.Noncompact.CompressionTube.LineInput_drive n M W := by
  intro b
  obtain ⟨ρ, hρc, hρ0, hρW, hρesc⟩ :=
    exists_escapingPath_of_spine hKsub hKuniv hspine htailW hqlev b
  obtain ⟨r, r', c, w, e, hr0, hr'0, he, hw, hc, hbc, hrcd, hr'cd, hrinj, hr'inj, hrp, hr'p,
    himm, himm', hrW, hr'W, hmeet, hrg, hr'g⟩ := htwo b ρ hρc hρW hρesc
  have hger : ∃ (c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (w' : EuclideanSpace ℝ (Fin n)) (e' : ℝ), 0 < e' ∧ w' ≠ 0 ∧
      c' ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder M ∧ ρ 0 ∈ c'.source ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ e' → r t = c'.symm (c' (ρ 0) + t • w')) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ e' → r' t = c'.symm (c' (ρ 0) + t • (-w'))) := by
    refine ⟨c, w, e, he, hw, hc, ?_, ?_, ?_⟩
    · exact hbc
    · intro t ht hte; exact hrg t ht hte
    · intro t ht hte; exact hr'g t ht hte
  obtain ⟨γ', hγ'sm, hγ'inj, hγ'prop, hγ'imm, hγ'1, hγ'sub⟩ :=
    Work.Drive.Rays.line_of_two_germed_oneSided_rays_drive (n := n)
      (b := ρ 0) hrcd hr'cd (by rw [hr0]) (by rw [hr'0]) hrinj hr'inj
      (fun x hx hx' => hmeet x hx hx')
      hrp hr'p (fun t ht => himm t (le_of_lt ht)) (fun t ht => himm' t (le_of_lt ht)) hger
  refine ⟨γ', by rw [hγ'1, hρ0], hγ'sm, hγ'inj, hγ'prop, hγ'imm, ?_⟩
  refine hγ'sub.trans (Set.union_subset ?_ ?_)
  · rintro x ⟨t, ht, rfl⟩; exact hrW t ht
  · rintro x ⟨t, ht, rfl⟩; exact hr'W t ht

/-! ### The line input from a single ray and the hairpin endgame -/

/-- **One escaping ray with a straight germ at `b`.** -/
def RayAt {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M] (W : Set M) (b : M) : Prop :=
  ∃ (r : ℝ → M) (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (w : EuclideanSpace ℝ (Fin n)) (e : ℝ),
    r 0 = b ∧ 0 < e ∧ w ≠ 0 ∧
    c ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M ∧ b ∈ c.source ∧
    ContMDiffOn Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder r (Set.Ici (0:ℝ)) ∧
    Set.InjOn r (Set.Ici (0:ℝ)) ∧
    IsProperMap (fun t : Set.Ici (0:ℝ) => r t) ∧
    (∀ t : ℝ, 0 ≤ t → Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n) r t)) ∧
    (∀ t : ℝ, 0 ≤ t → r t ∈ W) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ e → r t = c.symm (c b + t • w))

/-- **The line input from one escaping ray per base point and the hairpin endgame.**  The escaping
path of `exists_escapingPath_of_spine` at `b`, a smooth proper embedded ray along it
(`ray_by_truncation`) and the proved hairpin `Work.Drive.Rays.lineOfProperRay` give the smooth proper
embedded immersive line of `LineInput_drive`. -/
theorem lineInput_of_ray {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {B : Set M} {W : B → Set M} {K : ℕ → Set M} {lev : B → ℕ} {q : B → ℕ → M}
    {γ : B → ℕ → ℝ → M}
    (hWo : ∀ b, IsOpen (W b))
    (hKsub : ∀ i, K i ⊆ interior (K (i + 1)))
    (hKuniv : (⋃ i, K i) = (Set.univ : Set M))
    (hspine : Work.Noncompact.CompressionTube.SpineData K B lev q γ)
    (htailW : ∀ (b : B) (i : ℕ), lev b ≤ i →
      (⋃ j : {j : ℕ // i ≤ j}, γ b (j : ℕ) '' Set.Icc (0:ℝ) 1) ⊆ W b)
    (hqlev : ∀ b : B, q b (lev b) = (b : M))
    (hray : ∀ (b : B) (ρ : ℝ → M), Continuous ρ → (∀ t : ℝ, 0 ≤ t → ρ t ∈ W b) →
      (∀ K' : Set M, IsCompact K' → ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ρ t ∉ K') →
      ∃ r : ℝ → M, r 0 = ρ 0 ∧
        ContMDiffOn Work.Noncompact.CompressionTube.MCreal
          (Work.Noncompact.CompressionTube.MC n)
          Work.Noncompact.CompressionTube.smoothOrder r (Set.Ici (0:ℝ)) ∧
        Set.InjOn r (Set.Ici (0:ℝ)) ∧
        IsProperMap (fun t : Set.Ici (0:ℝ) => r t) ∧
        (∀ t : ℝ, 0 ≤ t → Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
          (Work.Noncompact.CompressionTube.MC n) r t)) ∧
        (∀ t : ℝ, 0 ≤ t → r t ∈ W b)) :
    Work.Noncompact.CompressionTube.LineInput_drive n M W := by
  intro b
  obtain ⟨ρ, hρc, hρ0, hρW, hρesc⟩ :=
    exists_escapingPath_of_spine hKsub hKuniv hspine htailW hqlev b
  obtain ⟨r, hr0, hrcd, hrinj, hrp, himm, hrW⟩ := hray b ρ hρc hρW hρesc
  obtain ⟨γ', hγ'1, hγ'sm, hγ'inj, hγ'prop, hγ'imm, hγ'sub⟩ :=
    Work.Drive.Rays.lineOfProperRay (n := n) hn (hWo b) hrcd hrinj hrp himm hrW
  exact ⟨γ', by rw [hγ'1, hr0, hρ0], hγ'sm, hγ'inj, hγ'prop, hγ'imm, hγ'sub⟩

/-- **The line input from one escaping *line* per base point.**  The same plumbing as
`lineInput_of_ray`, but the per-base-point input is the line itself (the corridor construction
`Work.Drive.lineOfEscapingPath_corridor`), so no hairpin endgame is needed. -/
theorem lineInput_of_line {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {B : Set M} {W : B → Set M} {K : ℕ → Set M} {lev : B → ℕ} {q : B → ℕ → M}
    {γ : B → ℕ → ℝ → M}
    (hWo : ∀ b, IsOpen (W b))
    (hKsub : ∀ i, K i ⊆ interior (K (i + 1)))
    (hKuniv : (⋃ i, K i) = (Set.univ : Set M))
    (hspine : Work.Noncompact.CompressionTube.SpineData K B lev q γ)
    (htailW : ∀ (b : B) (i : ℕ), lev b ≤ i →
      (⋃ j : {j : ℕ // i ≤ j}, γ b (j : ℕ) '' Set.Icc (0:ℝ) 1) ⊆ W b)
    (hqlev : ∀ b : B, q b (lev b) = (b : M))
    (hline : ∀ (b : B) (ρ : ℝ → M), Continuous ρ → (∀ t : ℝ, 0 ≤ t → ρ t ∈ W b) →
      (∀ K' : Set M, IsCompact K' → ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ρ t ∉ K') →
      ∃ γ' : ℝ → M, γ' 1 = ρ 0 ∧
        ContMDiff Work.Noncompact.CompressionTube.MCreal
          (Work.Noncompact.CompressionTube.MC n)
          Work.Noncompact.CompressionTube.smoothOrder γ' ∧
        Function.Injective γ' ∧ IsProperMap γ' ∧
        (∀ t : ℝ, Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
          (Work.Noncompact.CompressionTube.MC n) γ' t)) ∧
        Set.range γ' ⊆ W b) :
    Work.Noncompact.CompressionTube.LineInput_drive n M W := by
  intro b
  obtain ⟨ρ, hρc, hρ0, hρW, hρesc⟩ :=
    exists_escapingPath_of_spine hKsub hKuniv hspine htailW hqlev b
  obtain ⟨γ', h1, hsm, hinj, hprop, himm, hsub⟩ := hline b ρ hρc hρW hρesc
  exact ⟨γ', by rw [h1, hρ0], hsm, hinj, hprop, himm, hsub⟩

/-! ### The tube datum and the compression -/

/-- **The tube datum of the compression of the domain**, from the nested canals and the spine. -/
theorem exists_compression_tube_drive (n : ℕ) (hn : 2 ≤ n) (M : Type*)
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (hM : ¬ CompactSpace M) (B : Set M) (hB : ∀ K : Set M, IsCompact K → (B ∩ K).Finite) :
    Nonempty (Work.Noncompact.CompressionTube n M B) := by
  classical
  obtain ⟨K, W, D, lev, q, γ₀, hKc, -, hKsub, hKuniv, hWo, -, hWpc, -, hDo, hDpc, hDne,
    hDmono, hDsub, hDK, hWdisj, hWfin, hDnc, hspine, htail, hqlev⟩ :=
    Work.Noncompact.CompressionTube.exists_nested_canals (n := n) hn hM B hB
  -- the arcs from level `i` on stay in the canal
  have htailW : ∀ (b : B) (i : ℕ), lev b ≤ i →
      (⋃ j : {j : ℕ // i ≤ j}, γ₀ b (j : ℕ) '' Set.Icc (0:ℝ) 1) ⊆ W b :=
    fun b i hi => (htail b i hi).trans (hDsub b i)
  -- the lines inside the canals: through each base point an escaping path (the concatenated
  -- spine arcs), then one escaping ray along it (`ray_by_truncation`) and the hairpin endgame
  -- (`lineOfProperRay`) turning the ray into a line
  have hL : Work.Noncompact.CompressionTube.LineInput_drive n M W :=
    lineInput_of_line (n := n) hn hWo hKsub hKuniv hspine htailW hqlev
      (fun b ρ hρc hρW hρesc =>
        -- the ray design of the lead (H309) fixes `ray_by_truncation`; then the hairpin
        -- `lineOfProperRay` turns the ray into the line of `LineInput_drive`
        (by
          obtain ⟨r, hr0, hrsm, hrinj, hrp, hrimm, hrW⟩ :=
            ray_by_truncation (n := n) hn (hWo b) hρc hρW hρesc
          obtain ⟨γ', hγ'1, hγ'sm, hγ'inj, hγ'prop, hγ'imm, hγ'sub⟩ :=
            Work.Drive.Rays.lineOfProperRay (n := n) hn (hWo b) hrsm hrinj hrp hrimm hrW
          exact ⟨γ', by rw [hγ'1, hr0], hγ'sm, hγ'inj, hγ'prop, hγ'imm, hγ'sub⟩))
  -- a locally finite set is countable, hence indexable by a type in any prescribed universe
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  haveI : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
  have hBcount : B.Countable := by
    let E : CompactExhaustion M := CompactExhaustion.choice M
    have hBuniv : B = ⋃ i, B ∩ E i := by
      ext x
      simp only [mem_iUnion, mem_inter_iff, mem_univ]
      constructor
      · intro hx
        obtain ⟨i, hi⟩ := mem_iUnion.mp (E.iUnion_eq ▸ mem_univ x)
        exact ⟨i, hx, hi⟩
      · rintro ⟨i, hx, -⟩
        exact hx
    rw [hBuniv]
    exact Set.countable_iUnion fun i => (hB (E i) (E.isCompact i)).countable
  obtain ⟨f, hf⟩ := hBcount.exists_injective_nat
  -- the tube datum
  exact Work.Noncompact.CompressionTube.exists_compressionTube_of_lines_drive (n := n) hn
    hWo hWdisj hWfin hL (ULift.{_, 0} ↥(Set.range f))
    ((Equiv.ofInjective f hf).trans Equiv.ulift.symm)

open scoped Manifold ContDiff in
/-- The compression of the domain for a connected non-compact manifold, from the proved canals and
`Work.Drive.line_of_escaping_path`. -/
theorem hasCompression_drive (n : ℕ) (hn : 2 ≤ n) (M : Type*)
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (hM : ¬ CompactSpace M) : Work.Noncompact.HasCompression n M := by
  intro B hB
  have hT : Nonempty (Work.Noncompact.CompressionTube.{_, 0} n M B) :=
    exists_compression_tube_drive.{_, 0} (n := n) hn (M := M) hM B hB
  exact Work.Noncompact.CompressionTube.fromTube.{_, 0} (n := n) hn (Classical.choice hT)

end

end Work.Drive
