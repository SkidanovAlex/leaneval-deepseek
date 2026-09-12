import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_mem_intrinsicInterior_exposedFace
import Submission.Commons.Geometry.Convex.Hadwiger.finite_exposedFaces_convexHull
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_disjoint_intrinsicInterior_faces
import Submission.Commons.Geometry.Convex.Hadwiger.smear_frontier_cover

open Set Filter
open scoped Topology Convex Pointwise BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Commons.Geometry.Convex.Hadwiger

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V]

def prismSet (F : Set V) (v : V) : Set V :=
  {x : V | ∃ f ∈ F, ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x = f + t • v}

theorem mem_prismSet {F : Set V} {v x : V} :
    x ∈ prismSet F v ↔ ∃ f ∈ F, ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x = f + t • v := Iff.rfl

theorem prismSet_convex {F : Set V} (hF : Convex ℝ F) (v : V) :
    Convex ℝ (prismSet F v) := by
  rintro x ⟨f, hf, t, ht, rfl⟩ y ⟨f', hf', t', ht', rfl⟩ a b ha hb hab
  refine ⟨a • f + b • f', ?_, a • t + b • t', ?_, ?_⟩
  · exact hF hf hf' ha hb hab
  · exact (convex_Icc (0 : ℝ) 1) ht ht' ha hb hab
  · calc
      a • (f + t • v) + b • (f' + t' • v)
          = (a • f + a • (t • v)) + (b • f' + b • (t' • v)) := by rw [smul_add, smul_add]
      _ = (a • f + b • f') + (a • (t • v) + b • (t' • v)) := by abel
      _ = (a • f + b • f') + ((a * t) • v + (b * t') • v) := by
        rw [smul_smul, smul_smul]
      _ = (a • f + b • f') + (a • t + b • t') • v := by
        rw [add_smul]
        simp [smul_eq_mul]

theorem prismSet_isCompact {F : Set V} (hF : IsCompact F) (v : V) :
    IsCompact (prismSet F v) := by
  let g : V × ℝ → V := fun q => q.1 + q.2 • v
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have him : g '' (F ×ˢ Set.Icc (0 : ℝ) 1) = prismSet F v := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.1, hq.1, q.2, hq.2, rfl⟩
    · rintro ⟨f, hf, t, ht, rfl⟩
      refine ⟨(f, t), ⟨hf, ht⟩, rfl⟩
  rw [← him]
  exact IsCompact.image (hF.prod isCompact_Icc) hg

theorem prismSet_nonempty {F : Set V} (hF : F.Nonempty) (v : V) : (prismSet F v).Nonempty := by
  rcases hF with ⟨f, hf⟩
  refine ⟨f + (0 : ℝ) • v, f, hf, (0 : ℝ), ?_, rfl⟩
  exact left_mem_Icc.mpr zero_le_one

def prismBody {F : Set V} (hFcvx : Convex ℝ F) (hFcpt : IsCompact F) (hFne : F.Nonempty)
    (v : V) : ConvexBody V :=
  ⟨prismSet F v, prismSet_convex hFcvx v, prismSet_isCompact hFcpt v, prismSet_nonempty hFne v⟩

theorem prismBody_coe {F : Set V} (hFcvx : Convex ℝ F) (hFcpt : IsCompact F)
    (hFne : F.Nonempty) (v : V) : ((prismBody hFcvx hFcpt hFne v : ConvexBody V) : Set V) = prismSet F v :=
  rfl

def smearSet (P : Set V) (v : V) : Set V :=
  {x : V | ∃ p ∈ P, ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x = p + t • v}

theorem subset_smearSet_of_mem {P : Set V} {v : V} {x : V} (hx : x ∈ P) : x ∈ smearSet P v := by
  refine ⟨x, hx, (0 : ℝ), ?_, by simp⟩
  exact left_mem_Icc.mpr zero_le_one

theorem subset_smearSet_prism {P F : Set V} {v : V} (hFP : F ⊆ P) :
    prismSet F v ⊆ smearSet P v := by
  intro x hx
  rcases hx with ⟨f, hf, t, ht, rfl⟩
  exact ⟨f, hFP hf, t, ht, rfl⟩

theorem topFace_smul_pos {n : V} {P : Set V} {r : ℝ} (hr : 0 < r) :
    topFace (r • n) P = topFace n P := by
  ext x
  constructor <;> intro hx
  · rw [mem_topFace_iff] at hx ⊢
    rcases hx with ⟨hxP, hxle⟩
    refine ⟨hxP, ?_⟩
    intro y hy
    have hle' := hxle y hy
    have hy' : inner ℝ (r • n) y = r * inner ℝ n y := by
      rw [inner_smul_left]
      simp
    have hx' : inner ℝ (r • n) x = r * inner ℝ n x := by
      rw [inner_smul_left]
      simp
    rw [hy', hx'] at hle'
    exact (mul_le_mul_iff_of_pos_left hr).mp hle'
  · rw [mem_topFace_iff] at hx ⊢
    rcases hx with ⟨hxP, hxle⟩
    refine ⟨hxP, ?_⟩
    intro y hy
    have hy' : inner ℝ (r • n) y = r * inner ℝ n y := by
      rw [inner_smul_left]
      simp
    have hx' : inner ℝ (r • n) x = r * inner ℝ n x := by
      rw [inner_smul_left]
      simp
    rw [hy', hx']
    exact mul_le_mul_of_nonneg_left (hxle y hy) (le_of_lt hr)

theorem interior_level_const_empty {n : V} (hn : n ≠ 0) (c : ℝ) :
    interior {x : V | inner ℝ n x = c} = ∅ := by
  have hnn : inner ℝ n n ≠ 0 := by
    have : 0 < inner ℝ n n := real_inner_self_pos.mpr hn
    exact ne_of_gt this
  let q : V := (c / inner ℝ n n) • n
  have hcq : inner ℝ n q = c := by
    dsimp [q]
    rw [inner_smul_right]
    field_simp [hnn]
  have hset : {x : V | inner ℝ n x = c} = {x : V | inner ℝ n x = inner ℝ n q} := by
    ext x
    constructor
    · intro hx
      change inner ℝ n x = c at hx
      change inner ℝ n x = inner ℝ n q
      rw [hx]
      exact hcq.symm
    · intro hx
      change inner ℝ n x = inner ℝ n q at hx
      change inner ℝ n x = c
      rw [hx]
      exact hcq
  rw [hset]
  exact interior_level_empty_of_ne_zero hn

theorem interior_empty_of_subset_level {n : V} (hn : n ≠ 0) {A : Set V} {c : ℝ}
    (hA : A ⊆ {x : V | inner ℝ n x = c}) : interior A = ∅ := by
  have hint := interior_mono hA
  rw [interior_level_const_empty hn c] at hint
  exact eq_empty_of_subset_empty hint

theorem interior_inter_prismSet_topFace_eq_empty {P F : Set V} {n v : V}
    (hF : F = topFace n P) (hn : n ≠ 0) (hv : 0 ≤ inner ℝ n v) (hFn : F.Nonempty) :
    interior (P ∩ prismSet F v) = ∅ := by
  rcases hFn with ⟨f0, hf0⟩
  have hf0T : f0 ∈ topFace n P := by simpa [hF] using hf0
  have hsub : P ∩ prismSet F v ⊆ {x : V | inner ℝ n x = inner ℝ n f0} := by
    intro x hx
    rcases hx with ⟨hxP, hxpr⟩
    change x ∈ prismSet F v at hxpr
    rcases hxpr with ⟨f, hf, t, ht, rfl⟩
    have hfT : f ∈ topFace n P := by simpa [hF] using hf
    have hℓeq : inner ℝ n f = inner ℝ n f0 := topFace_eq_of_mem hfT hf0T
    have hle : inner ℝ n (f + t • v) ≤ inner ℝ n f0 := topFace_le_of_mem hf0T hxP
    have hnonneg : 0 ≤ t * inner ℝ n v := mul_nonneg ht.1 hv
    have hge : inner ℝ n f0 ≤ inner ℝ n (f + t • v) := by
      rw [inner_add_right, inner_smul_right, hℓeq]
      linarith
    exact le_antisymm hle hge
  exact interior_empty_of_subset_level hn hsub

theorem interior_prismSet_topFace_eq_empty_of_zero {P F : Set V} {n v : V}
    (hF : F = topFace n P) (hn : n ≠ 0) (hv : inner ℝ n v = 0) (hFn : F.Nonempty) :
    interior (prismSet F v) = ∅ := by
  rcases hFn with ⟨f0, hf0⟩
  have hf0T : f0 ∈ topFace n P := by simpa [hF] using hf0
  have hsub : prismSet F v ⊆ {x : V | inner ℝ n x = inner ℝ n f0} := by
    intro x hx
    change x ∈ prismSet F v at hx
    rcases hx with ⟨f, hf, t, ht, rfl⟩
    have hfT : f ∈ topFace n P := by simpa [hF] using hf
    have hℓeq : inner ℝ n f = inner ℝ n f0 := topFace_eq_of_mem hfT hf0T
    have hgoal : inner ℝ n (f + t • v) = inner ℝ n f0 := by
      rw [inner_add_right, inner_smul_right, hℓeq, hv]
      simp
    change inner ℝ n (f + t • v) = inner ℝ n f0
    exact hgoal
  exact interior_empty_of_subset_level hn hsub

theorem prismSet_inter_subset_level {P F G : Set V} {n m v : V}
    (hF : F = topFace n P) (hG : G = topFace m P)
    {f0 : V} (hf0 : f0 ∈ F) {g0 : V} (hg0 : g0 ∈ G)
    (hcF : 0 < inner ℝ n v) (hcG : 0 < inner ℝ m v) :
    prismSet F v ∩ prismSet G v ⊆
      {x : V | inner ℝ ((inner ℝ m v) • n - (inner ℝ n v) • m) x =
          (inner ℝ m v) * (inner ℝ n f0) - (inner ℝ n v) * (inner ℝ m g0)} := by
  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  change x ∈ prismSet F v at hx1
  change x ∈ prismSet G v at hx2
  rcases hx1 with ⟨f, hf, t, ht, rfl⟩
  rcases hx2 with ⟨g, hg, s, hs, hxs⟩
  have hfT : f ∈ topFace n P := by simpa [hF] using hf
  have hgT : g ∈ topFace m P := by simpa [hG] using hg
  have hf0T : f0 ∈ topFace n P := by simpa [hF] using hf0
  have hg0T : g0 ∈ topFace m P := by simpa [hG] using hg0
  have hfeq : inner ℝ n f = inner ℝ n f0 := topFace_eq_of_mem hfT hf0T
  have hgeq : inner ℝ m g = inner ℝ m g0 := topFace_eq_of_mem hgT hg0T
  have hgP : g ∈ P := topFace_subset hgT
  have hfP : f ∈ P := topFace_subset hfT
  have hts : t = s := by
    apply le_antisymm
    · have hmain : inner ℝ n (f + t • v) = inner ℝ n (g + s • v) := by rw [hxs]
      rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right, hfeq] at hmain
      have hg_le : inner ℝ n g ≤ inner ℝ n f0 := topFace_le_of_mem hf0T hgP
      have hc : 0 < inner ℝ n v := hcF
      have hcalc : t * inner ℝ n v = (inner ℝ n g - inner ℝ n f0) + s * inner ℝ n v := by
        linarith
      have hprod : inner ℝ n v * t ≤ inner ℝ n v * s := by
        nlinarith [hcalc, hg_le]
      exact (mul_le_mul_iff_of_pos_left hc).mp hprod
    · have hmain : inner ℝ m (f + t • v) = inner ℝ m (g + s • v) := by rw [hxs]
      rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right, hgeq] at hmain
      have hf_le : inner ℝ m f ≤ inner ℝ m g0 := topFace_le_of_mem hg0T hfP
      have hc : 0 < inner ℝ m v := hcG
      have hcalc : s * inner ℝ m v = (inner ℝ m f - inner ℝ m g0) + t * inner ℝ m v := by
        linarith
      have hprod : inner ℝ m v * s ≤ inner ℝ m v * t := by
        nlinarith [hcalc, hf_le]
      exact (mul_le_mul_iff_of_pos_left hc).mp hprod
  subst s
  have hg_eq_f : g = f := by
    have : (g + t • v) - (f + t • v) = g - f := by abel
    have h0 : (g + t • v) - (f + t • v) = 0 := by
      rw [← hxs]
      abel
    rw [this] at h0
    exact sub_eq_zero.mp h0
  subst g
  change inner ℝ ((inner ℝ m v) • n - (inner ℝ n v) • m) (f + t • v) =
    (inner ℝ m v) * (inner ℝ n f0) - (inner ℝ n v) * (inner ℝ m g0)
  rw [inner_sub_left, inner_smul_left, inner_smul_left, inner_add_right, inner_smul_right,
    inner_add_right, inner_smul_right, hfeq, hgeq]
  simp
  ring

theorem interior_inter_prismSet_prismSet_eq_empty {P F G : Set V} {n m v : V}
    (hF : F = topFace n P) (hG : G = topFace m P)
    (hn : n ≠ 0) (hm : m ≠ 0)
    (hv : 0 ≤ inner ℝ n v) (hw : 0 ≤ inner ℝ m v)
    (hFn : F.Nonempty) (hGn : G.Nonempty) (hFG : F ≠ G) :
    interior (prismSet F v ∩ prismSet G v) = ∅ := by
  by_cases hcF0 : inner ℝ n v = 0
  · have hintF : interior (prismSet F v) = ∅ :=
      interior_prismSet_topFace_eq_empty_of_zero (P := P) (F := F) (n := n) (v := v) hF hn hcF0 hFn
    have hsub : interior (prismSet F v ∩ prismSet G v) ⊆ interior (prismSet F v) :=
      interior_mono (inter_subset_left : prismSet F v ∩ prismSet G v ⊆ prismSet F v)
    rw [hintF] at hsub
    exact eq_empty_of_subset_empty hsub
  by_cases hcG0 : inner ℝ m v = 0
  · have hintG : interior (prismSet G v) = ∅ :=
      interior_prismSet_topFace_eq_empty_of_zero (P := P) (F := G) (n := m) (v := v) hG hm hcG0 hGn
    have hsub : interior (prismSet F v ∩ prismSet G v) ⊆ interior (prismSet G v) :=
      interior_mono (inter_subset_right : prismSet F v ∩ prismSet G v ⊆ prismSet G v)
    rw [hintG] at hsub
    exact eq_empty_of_subset_empty hsub
  have hcFpos : 0 < inner ℝ n v := lt_of_le_of_ne hv (Ne.symm hcF0)
  have hcGpos : 0 < inner ℝ m v := lt_of_le_of_ne hw (Ne.symm hcG0)
  rcases hFn with ⟨f0, hf0⟩
  rcases hGn with ⟨g0, hg0⟩
  let eta : V := (inner ℝ m v) • n - (inner ℝ n v) • m
  have heta_ne : eta ≠ 0 := by
    intro heta0
    have h : (inner ℝ m v) • n = (inner ℝ n v) • m := by
      dsimp [eta] at heta0
      exact sub_eq_zero.mp heta0
    have hn : n = ((inner ℝ m v)⁻¹ * inner ℝ n v) • m := by
      calc
        n = ((inner ℝ m v)⁻¹) • ((inner ℝ m v) • n) := by
          rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hcGpos), one_smul]
        _ = ((inner ℝ m v)⁻¹) • ((inner ℝ n v) • m) := by rw [h]
        _ = ((inner ℝ m v)⁻¹ * inner ℝ n v) • m := by rw [smul_smul]
    have hpos : 0 < (inner ℝ m v)⁻¹ * inner ℝ n v :=
      mul_pos (inv_pos.mpr hcGpos) hcFpos
    have htop : topFace n P = topFace m P := by
      rw [hn]
      exact topFace_smul_pos hpos
    have hFG' : F = G := by
      calc
        F = topFace n P := hF
        _ = topFace m P := htop
        _ = G := hG.symm
    exact hFG hFG'
  have hsub := prismSet_inter_subset_level (P := P) (F := F) (G := G) (n := n) (m := m) (v := v)
    hF hG hf0 hg0 hcFpos hcGpos
  have hintsub : interior (prismSet F v ∩ prismSet G v) ⊆
      interior {x : V | inner ℝ eta x =
        (inner ℝ m v) * (inner ℝ n f0) - (inner ℝ n v) * (inner ℝ m g0)} := by
    apply interior_mono
    intro x hxmem
    have hs2 := hsub hxmem
    dsimp [eta] at hs2 ⊢
    change inner ℝ ((inner ℝ m v) • n - (inner ℝ n v) • m) x =
      (inner ℝ m v) * (inner ℝ n f0) - (inner ℝ n v) * (inner ℝ m g0)
    exact hs2
  rw [interior_level_const_empty heta_ne ((inner ℝ m v) * (inner ℝ n f0) - (inner ℝ n v) * (inner ℝ m g0))] at hintsub
  exact eq_empty_of_subset_empty hintsub


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V]

/-- A nonzero functional is not constant on a full-dimensional set. -/
theorem topFace_ne_P_of_ne_zero {P : Set V} (hPint : (interior P).Nonempty) {n : V} (hn : n ≠ 0) :
    topFace n P ≠ P := by
  intro htop
  rcases hPint with ⟨c, hcint⟩
  have hcP : c ∈ P := interior_subset hcint
  have hnpos : 0 < inner ℝ n n := real_inner_self_pos.mpr hn
  have hball : ∃ r : ℝ, 0 < r ∧ Metric.ball c r ⊆ interior P := by
    exact Metric.isOpen_iff.mp isOpen_interior c hcint
  rcases hball with ⟨r, hr, hballsub⟩
  let ε : ℝ := r / (2 * ‖n‖)
  have hε0 : 0 < ε := by
    dsimp [ε]
    exact div_pos hr (mul_pos (by norm_num) (norm_pos_iff.mpr hn))
  have hballc : c + ε • n ∈ Metric.ball c r := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hnorm : ‖(c + ε • n) - c‖ < r := by
      rw [add_sub_cancel_left, norm_smul]
      rw [Real.norm_eq_abs, abs_of_pos hε0]
      dsimp [ε]
      have hdiv : r / (2 * ‖n‖) * ‖n‖ = r / 2 := by
        field_simp [norm_pos_iff.mpr hn]
      rw [hdiv]
      linarith
    exact hnorm
  have hc'int : c + ε • n ∈ interior P := hballsub hballc
  have hc'P : c + ε • n ∈ P := interior_subset hc'int
  have hcT : c ∈ topFace n P := by simpa [htop] using hcP
  have hc'T : c + ε • n ∈ topFace n P := by simpa [htop] using hc'P
  have heq : inner ℝ n c = inner ℝ n (c + ε • n) := topFace_eq_of_mem hcT hc'T
  have hcalc : inner ℝ n (c + ε • n) = inner ℝ n c + ε * inner ℝ n n := by
    rw [inner_add_right, inner_smul_right]
  have hεnn : ε * inner ℝ n n ≠ 0 := by
    exact mul_ne_zero (ne_of_gt hε0) (ne_of_gt hnpos)
  nlinarith

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V]

/-- Covering lemma for the smear of a compact convex set: a point of the smear
outside `P` lies in the prism over a `v`-forward exposed face of `P`. -/
theorem local_cover {P : Set V} (hPconv : Convex ℝ P) (hPcpt : IsCompact P) (v x : V)
    (hxS : ∃ p ∈ P, ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x = p + t • v)
    (hxP : x ∉ P) :
    ∃ n : V, n ≠ 0 ∧ 0 ≤ inner ℝ n v ∧
      ∃ f ∈ topFace n P, ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x = f + t • v := by
  rcases smear_frontier_cover (P := P) hPconv hPcpt v x hxS hxP with ⟨n, hn0, hnv, f, hf, t, ht, hxeq⟩
  refine ⟨n, hn0, hnv, f, ?_, t, ht, hxeq⟩
  simpa [topFace] using hf

/-- The smear `P + [0,1]·v` of a full-dimensional polytope is the union of `P`
with the prisms over the `v`-forward exposed faces, any two pieces meeting with
empty interior. -/
theorem polytope_smear_dissection
    (n : ℕ) (u : Finset (EuclideanSpace ℝ (Fin n))) (P : Set (EuclideanSpace ℝ (Fin n)))
    (hP : P = convexHull ℝ (u : Set (EuclideanSpace ℝ (Fin n))))
    (hint : (interior P).Nonempty)
    (v : EuclideanSpace ℝ (Fin n)) :
    ∃ ι : Type, ∃ _ : Fintype ι, ∃ Q : ι → ConvexBody (EuclideanSpace ℝ (Fin n)),
      (∀ i : ι, ∃ F : Set (EuclideanSpace ℝ (Fin n)), F.Nonempty ∧ IsExposed ℝ P F ∧ F ≠ P ∧
        ((Q i : Set (EuclideanSpace ℝ (Fin n))) =
          {x : EuclideanSpace ℝ (Fin n) | ∃ f : EuclideanSpace ℝ (Fin n), f ∈ F ∧
            ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x = f + t • v})) ∧
      ({x : EuclideanSpace ℝ (Fin n) | ∃ p : EuclideanSpace ℝ (Fin n), p ∈ P ∧
          ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x = p + t • v} =
        P ∪ ⋃ i : ι, (Q i : Set (EuclideanSpace ℝ (Fin n)))) ∧
      (∀ i : ι, interior (P ∩ (Q i : Set (EuclideanSpace ℝ (Fin n)))) = ∅) ∧
      (∀ i j : ι, i ≠ j → interior ((Q i : Set (EuclideanSpace ℝ (Fin n))) ∩ (Q j : Set (EuclideanSpace ℝ (Fin n)))) = ∅) := by
  classical
  let E : Type := EuclideanSpace ℝ (Fin n)
  let fam : Set (Set E) := {F : Set E | F.Nonempty ∧ IsExposed ℝ P F ∧ F ≠ P ∧
      ∃ w : E, w ≠ 0 ∧ F = topFace w P ∧ 0 ≤ inner ℝ w v}
  have hfam_sub : fam ⊆ {F : Set E | IsExposed ℝ P F ∧ F.Nonempty ∧ F ≠ P} := by
    intro F hF
    exact ⟨hF.2.1, hF.1, hF.2.2.1⟩
  have hfam_fin : fam.Finite := (finite_exposedFaces_convexHull n u P hP).subset hfam_sub
  let ι : Type := {F : Set E // F ∈ fam}
  haveI : Fintype ι := hfam_fin.fintype
  have hPcvx : Convex ℝ P := by
    rw [hP]
    exact convex_convexHull ℝ (u : Set E)
  have hPcpt : IsCompact P := by
    rw [hP]
    exact (Finset.finite_toSet u).isCompact_convexHull ℝ
  have faceConv : ∀ F : Set E, F ∈ fam → Convex ℝ F := by
    intro F hF
    exact (hF.2.1).convex hPcvx
  have faceCpt : ∀ F : Set E, F ∈ fam → IsCompact F := by
    intro F hF
    rcases hF with ⟨hFne, hFexp, hFneP, hFw⟩
    have hFcv := polytope_exposedFace_conv_vertices n u P hP hFexp hFne
    rw [hFcv]
    exact ((Finset.finite_toSet u).subset (by intro x hx; exact hx.2)).isCompact_convexHull ℝ
  let Q : ι → ConvexBody E := fun i => prismBody (faceConv i.1 i.2) (faceCpt i.1 i.2) (i.2).1 v
  have hQco : ∀ i : ι, (Q i : Set E) = prismSet (i.1 : Set E) v := by
    intro i
    simp [Q, prismBody_coe]
  -- (a) each piece is a prism over a proper nonempty exposed face
  have hQface : ∀ i : ι, ∃ F : Set E, F.Nonempty ∧ IsExposed ℝ P F ∧ F ≠ P ∧
      ((Q i : Set E) = {x : E | ∃ f : E, f ∈ F ∧ ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x = f + t • v}) := by
    intro i
    refine ⟨(i.1 : Set E), ?_, ?_, ?_, ?_⟩
    · exact (i.2).1
    · exact (i.2).2.1
    · exact (i.2).2.2.1
    · change (Q i : Set E) = prismSet (i.1 : Set E) v
      exact hQco i
  -- (c) each piece meets P with empty interior
  have hinterP : ∀ i : ι, interior (P ∩ (Q i : Set E)) = ∅ := by
    intro i
    rcases (i.2) with ⟨hFne, hFexp, hFneP, hFw⟩
    rcases hFw with ⟨w, hw0, hFw, hwv⟩
    rw [hQco i]
    exact interior_inter_prismSet_topFace_eq_empty (P := P) (F := (i.1 : Set E)) (n := w) (v := v)
      hFw hw0 hwv hFne
  -- (d) distinct pieces meet with empty interior
  have hpair : ∀ i j : ι, i ≠ j → interior ((Q i : Set E) ∩ (Q j : Set E)) = ∅ := by
    intro i j hij
    have hface_ne : (i.1 : Set E) ≠ j.1 := by
      intro h
      apply hij
      exact Subtype.ext h
    rcases (i.2) with ⟨hFne, hFexp, hFneP, hFw⟩
    rcases hFw with ⟨w, hw0, hFw, hwv⟩
    rcases (j.2) with ⟨hGne, hGexp, hGneP, hGw⟩
    rcases hGw with ⟨m, hm0, hGm, hmv⟩
    rw [hQco i, hQco j]
    exact interior_inter_prismSet_prismSet_eq_empty (P := P) (F := (i.1 : Set E)) (G := (j.1 : Set E))
      (n := w) (m := m) (v := v) hFw hGm hw0 hm0 hwv hmv hFne hGne hface_ne
  -- (b) the union identity
  have hsub_union : P ∪ ⋃ i : ι, (Q i : Set E) ⊆ smearSet P v := by
    apply Set.union_subset
    · intro x hx
      exact subset_smearSet_of_mem hx
    · apply Set.iUnion_subset
      intro i
      rw [hQco i]
      exact subset_smearSet_prism (P := P) (F := (i.1 : Set E)) (v := v) ((i.2).2.1.subset)
  have hcover : smearSet P v ⊆ P ∪ ⋃ i : ι, (Q i : Set E) := by
    intro x hxS
    by_cases hxP : x ∈ P
    · exact Or.inl hxP
    · right
      rcases local_cover (P := P) hPcvx hPcpt v x hxS hxP with ⟨w, hw0, hwv, f, hf, t, ht, hxeq⟩
      let Fw : Set E := topFace w P
      have hFw_exp : IsExposed ℝ P Fw := by
        simpa [Fw] using isExposed_topFace w P
      have hFw_ne : Fw.Nonempty := ⟨f, hf⟩
      have hFw_pp : Fw ≠ P := by
        exact topFace_ne_P_of_ne_zero (P := P) hint hw0
      have hFw_mem : Fw ∈ fam := by
        change Fw.Nonempty ∧ IsExposed ℝ P Fw ∧ Fw ≠ P ∧
          ∃ w' : E, w' ≠ 0 ∧ Fw = topFace w' P ∧ 0 ≤ inner ℝ w' v
        exact ⟨hFw_ne, hFw_exp, hFw_pp, w, hw0, rfl, hwv⟩
      let i : ι := ⟨Fw, hFw_mem⟩
      have hxQi : x ∈ (Q i : Set E) := by
        rw [hQco i]
        change x ∈ prismSet Fw v
        exact ⟨f, hf, t, ht, hxeq⟩
      exact Set.mem_iUnion.mpr ⟨i, hxQi⟩
  have hunion : smearSet P v = P ∪ ⋃ i : ι, (Q i : Set E) :=
    Subset.antisymm hcover hsub_union
  refine ⟨ι, hfam_fin.fintype, Q, ?_, ?_, ?_, ?_⟩
  · -- per-face statement, translated to the literal E type
    intro i
    rcases hQface i with ⟨F, hFne, hFexp, hFneP, hFcar⟩
    refine ⟨F, hFne, hFexp, hFneP, ?_⟩
    change (Q i : Set (EuclideanSpace ℝ (Fin n))) =
      {x : EuclideanSpace ℝ (Fin n) | ∃ f : EuclideanSpace ℝ (Fin n), f ∈ F ∧
        ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x = f + t • v}
    simpa [E] using hFcar
  · -- union identity
    change {x : EuclideanSpace ℝ (Fin n) | ∃ p : EuclideanSpace ℝ (Fin n), p ∈ P ∧
        ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x = p + t • v} =
      P ∪ ⋃ i : ι, (Q i : Set (EuclideanSpace ℝ (Fin n)))
    simpa [E, smearSet] using hunion
  · intro i
    change interior (P ∩ (Q i : Set (EuclideanSpace ℝ (Fin n)))) = ∅
    simpa [E] using hinterP i
  · intro i j hij
    change interior ((Q i : Set (EuclideanSpace ℝ (Fin n))) ∩ (Q j : Set (EuclideanSpace ℝ (Fin n)))) = ∅
    simpa [E] using hpair i j hij

end

end

end Commons.Geometry.Convex.Hadwiger
