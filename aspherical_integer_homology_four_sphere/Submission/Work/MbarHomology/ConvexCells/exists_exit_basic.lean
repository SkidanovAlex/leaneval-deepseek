import Mathlib
import Submission.Work.MbarHomology.ConvexCells.sd_carrier_of_basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The radial exit lemma, from the basic checks only

`Work.ConvexCells.exists_exit` proves the radial exit lemma for a polytope satisfying the full
`P.Ok` (which bundles `OkBasic`, `OkEmp` and `OkAdd`).  In fact the argument only ever uses the
`pos`, denominator and boundedness parts of `OkBasic`; the emptiness and adding-constraint
certificates are irrelevant.  This file ports `Work.ConvexCells.exists_exit` to the `OkBasic`
hypothesis, reusing the `OkBasic` accessors of
`Submission.Work.MbarHomology.ConvexCells.sd_carrier_of_basic`.

The mathematical content is unchanged: for a point `x` of the closed face `Fset f` whose tight set
is exactly `tight f` (so `x` lies in the relative interior of the face), the ray from the interior
point `posR f` through `x` meets the polytope in a closed interval `[0, t]` with `t > 1`; the exit
point `r = posR f + t • (x - posR f)` lies in the face and a new constraint becomes tight there.
-/

namespace Work.MbarHomology.ConvexCells

open Work.ConvexCells
open Work.ConvexCells.PolytopeData
open scoped BigOperators

variable {d : ℕ}

/-! ### `OkBasic` accessors for the boundedness certificate -/

theorem okBasic_bndPos_nonneg (P : PolytopeData d) (h : P.OkBasic) (j : Fin d) (k : Fin P.m) :
    0 ≤ P.bndPos j k := h.2.2.2.2.2.1 j k

theorem okBasic_bndNeg_nonneg (P : PolytopeData d) (h : P.OkBasic) (j : Fin d) (k : Fin P.m) :
    0 ≤ P.bndNeg j k := h.2.2.2.2.2.2.1 j k

theorem okBasic_bndPos_vec (P : PolytopeData d) (h : P.OkBasic) (j j' : Fin d) :
    ∑ k, P.bndPos j k * P.nrm k j' = (P.D : ℤ) * (if j = j' then 1 else 0) :=
  h.2.2.2.2.2.2.2.1 j j'

theorem okBasic_bndNeg_vec (P : PolytopeData d) (h : P.OkBasic) (j j' : Fin d) :
    ∑ k, P.bndNeg j k * P.nrm k j' = (P.D : ℤ) * (if j = j' then -1 else 0) :=
  h.2.2.2.2.2.2.2.2 j j'

/-- The `pos` point of a face lies in the closed face, from the basic checks. -/
theorem posR_mem_Fset_basic (P : PolytopeData d) (h : P.OkBasic) (f : Fin P.K) :
    P.posR f ∈ P.Fset f :=
  ⟨Work.ConvexCells.posR_mem_Pset_basic h f, fun i hi =>
    Work.ConvexCells.inner_nR_posR_of_mem_basic h f i hi⟩

/-! ### Boundedness of `Pset` from the `OkBasic` certificate -/

/-- The boundedness certificate in real form: `∑ k bndPos j k • nR k = e_j`. -/
theorem bndPos_sum_basic (P : PolytopeData d) (h : P.OkBasic) (j : Fin d) :
    ∑ k, (P.bndPos j k : ℝ) • P.nR k = basisVec j := by
  have hDne : (P.D : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Work.ConvexCells.okBasic_D_pos h))
  have hcomb : (∑ k, P.bndPos j k • P.nrm k) = (P.D : ℤ) • Pi.single j (1 : ℤ) := by
    ext j'
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [okBasic_bndPos_vec P h j j']
    by_cases hjj : j' = j
    · rw [hjj]; simp
    · rw [ite_eq_right (fun hh => hjj hh.symm), Pi.single_eq_of_ne hjj]
  calc ∑ k, (P.bndPos j k : ℝ) • P.nR k
      = ∑ k, ((P.D : ℝ))⁻¹ • ((P.bndPos j k : ℝ) • toE (P.nrm k)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [nR, smul_comm]
    _ = ((P.D : ℝ))⁻¹ • ∑ k, (P.bndPos j k : ℝ) • toE (P.nrm k) :=
        (Finset.smul_sum (s := Finset.univ)).symm
    _ = ((P.D : ℝ))⁻¹ • ∑ k, toE (P.bndPos j k • P.nrm k) := by
        congr 1
        exact Finset.sum_congr rfl fun k _ => (toE_smul (P.bndPos j k) (P.nrm k)).symm
    _ = ((P.D : ℝ))⁻¹ • toE (∑ k, P.bndPos j k • P.nrm k) := by rw [← toE_sum]
    _ = ((P.D : ℝ))⁻¹ • toE ((P.D : ℤ) • Pi.single j (1 : ℤ)) := by rw [hcomb]
    _ = ((P.D : ℝ))⁻¹ • ((P.D : ℝ) • basisVec j) := by rw [toE_smul]; rfl
    _ = basisVec j := by rw [smul_smul, inv_mul_cancel₀ hDne, one_smul]

/-- The boundedness certificate in real form: `∑ k bndNeg j k • nR k = -e_j`. -/
theorem bndNeg_sum_basic (P : PolytopeData d) (h : P.OkBasic) (j : Fin d) :
    ∑ k, (P.bndNeg j k : ℝ) • P.nR k = - basisVec j := by
  have hDne : (P.D : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Work.ConvexCells.okBasic_D_pos h))
  have hcomb : (∑ k, P.bndNeg j k • P.nrm k) = (P.D : ℤ) • Pi.single j (-1 : ℤ) := by
    ext j'
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [okBasic_bndNeg_vec P h j j']
    by_cases hjj : j' = j
    · rw [hjj]; simp
    · rw [ite_eq_right (fun hh => hjj hh.symm), Pi.single_eq_of_ne hjj]
  have hsingle : toE (Pi.single j (-1 : ℤ)) = - basisVec j := by
    have h1 : Pi.single j (-1 : ℤ) = - Pi.single (M := fun _ => ℤ) j (1 : ℤ) := by
      funext j'
      by_cases hh : j' = j <;> simp [Pi.single_eq_same, Pi.single_eq_of_ne, hh]
    rw [h1, toE_neg]; rfl
  calc ∑ k, (P.bndNeg j k : ℝ) • P.nR k
      = ∑ k, ((P.D : ℝ))⁻¹ • ((P.bndNeg j k : ℝ) • toE (P.nrm k)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [nR, smul_comm]
    _ = ((P.D : ℝ))⁻¹ • ∑ k, (P.bndNeg j k : ℝ) • toE (P.nrm k) :=
        (Finset.smul_sum (s := Finset.univ)).symm
    _ = ((P.D : ℝ))⁻¹ • ∑ k, toE (P.bndNeg j k • P.nrm k) := by
        congr 1
        exact Finset.sum_congr rfl fun k _ => (toE_smul (P.bndNeg j k) (P.nrm k)).symm
    _ = ((P.D : ℝ))⁻¹ • toE (∑ k, P.bndNeg j k • P.nrm k) := by rw [← toE_sum]
    _ = ((P.D : ℝ))⁻¹ • toE ((P.D : ℤ) • Pi.single j (-1 : ℤ)) := by rw [hcomb]
    _ = ((P.D : ℝ))⁻¹ • ((P.D : ℝ) • (- basisVec j)) := by rw [toE_smul, hsingle]; rfl
    _ = - basisVec j := by rw [smul_smul, inv_mul_cancel₀ hDne, one_smul]

/-- Coordinate upper bounds from the boundedness certificate. -/
theorem coord_le_basic (P : PolytopeData d) (h : P.OkBasic) {x : E d} (hx : x ∈ P.Pset)
    (j : Fin d) : x j ≤ ∑ k, (P.bndPos j k : ℝ) * P.bR k := by
  have h1 : x j = ∑ k, (P.bndPos j k : ℝ) * inner ℝ (P.nR k) x := by
    rw [← inner_basisVec j x, ← bndPos_sum_basic P h j, inner_lincomb_left]
  rw [h1]
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_left (hx k) (Int.cast_nonneg (okBasic_bndPos_nonneg P h j k))

/-- Coordinate lower bounds from the boundedness certificate. -/
theorem neg_coord_le_basic (P : PolytopeData d) (h : P.OkBasic) {x : E d} (hx : x ∈ P.Pset)
    (j : Fin d) : -(x j) ≤ ∑ k, (P.bndNeg j k : ℝ) * P.bR k := by
  have hb : basisVec j = -∑ k, (P.bndNeg j k : ℝ) • P.nR k := by
    rw [bndNeg_sum_basic P h j, neg_neg]
  have h1 : -(x j) = ∑ k, (P.bndNeg j k : ℝ) * inner ℝ (P.nR k) x := by
    have h2 : x j = -∑ k, (P.bndNeg j k : ℝ) * inner ℝ (P.nR k) x := by
      rw [← inner_basisVec j x, hb, inner_neg_left, inner_lincomb_left]
    rw [h2, neg_neg]
  rw [h1]
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_left (hx k) (Int.cast_nonneg (okBasic_bndNeg_nonneg P h j k))

/-- `Pset` is bounded, from the boundedness certificate of `OkBasic`. -/
theorem Pset_bounded_basic (P : PolytopeData d) (h : P.OkBasic) :
    ∃ R, P.Pset ⊆ Metric.closedBall (0 : E d) R := by
  refine ⟨Real.sqrt (∑ j, (|∑ k, (P.bndPos j k : ℝ) * P.bR k|
      + |∑ k, (P.bndNeg j k : ℝ) * P.bR k|) ^ 2), ?_⟩
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right,
    show ‖x‖ = Real.sqrt (‖x‖ ^ 2) from (Real.sqrt_sq (norm_nonneg x)).symm]
  refine Real.sqrt_le_sqrt ?_
  rw [EuclideanSpace.real_norm_sq_eq]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 := coord_le_basic P h hx j
  have h2 := neg_coord_le_basic P h hx j
  have h3 : |x j| ≤ |∑ k, (P.bndPos j k : ℝ) * P.bR k|
      + |∑ k, (P.bndNeg j k : ℝ) * P.bR k| := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · have hB : (∑ k, (P.bndNeg j k : ℝ) * P.bR k)
          ≤ |∑ k, (P.bndNeg j k : ℝ) * P.bR k| := le_abs_self _
      have h0 : (0:ℝ) ≤ |∑ k, (P.bndPos j k : ℝ) * P.bR k| := abs_nonneg _
      linarith
    · have hB : (0:ℝ) ≤ |∑ k, (P.bndNeg j k : ℝ) * P.bR k| := abs_nonneg _
      have hC : (∑ k, (P.bndPos j k : ℝ) * P.bR k)
          ≤ |∑ k, (P.bndPos j k : ℝ) * P.bR k| := le_abs_self _
      linarith
  rw [← sq_abs (x j)]
  exact pow_le_pow_left₀ (abs_nonneg _) h3 2

/-! ### The ray through a face -/

/-- On the whole ray from `posR f` through a point `x` of the face `f`, every constraint of
`tight f` stays tight. -/
theorem ray_tight_basic (P : PolytopeData d) (h : P.OkBasic) (f : Fin P.K) {x : E d}
    (hx : x ∈ P.Fset f) {i : Fin P.m} (hi : i ∈ P.tight f) (s : ℝ) :
    inner ℝ (P.nR i) (P.posR f + s • (x - P.posR f)) = P.bR i := by
  have hxE : inner ℝ (P.nR i) x = P.bR i := hx.2 i hi
  have hpE : inner ℝ (P.nR i) (P.posR f) = P.bR i := (posR_mem_Fset_basic P h f).2 i hi
  rw [inner_add_right, inner_smul_right, inner_sub_right, hxE, hpE]
  ring

/-- The ray through the point `x ∈ Fset f` can be extended a little beyond the parameter `s₀`,
provided the point `posR f + s₀ • (x - posR f)` strictly satisfies every constraint that is
not in `tight f`. -/
theorem ray_extends_basic (P : PolytopeData d) (h : P.OkBasic) (f : Fin P.K) {x : E d}
    (hx : x ∈ P.Fset f) (s₀ : ℝ)
    (hstrict : ∀ i, i ∉ P.tight f →
      inner ℝ (P.nR i) (P.posR f + s₀ • (x - P.posR f)) < P.bR i) :
    ∃ δ, 0 < δ ∧ P.posR f + (s₀ + δ) • (x - P.posR f) ∈ P.Pset := by
  set I : Finset (Fin P.m) := Finset.univ.filter (fun i => i ∉ P.tight f) with hI
  have hImem : ∀ i, i ∈ I ↔ i ∉ P.tight f := by
    intro i; rw [hI, Finset.mem_filter]; simp
  by_cases hIne : I.Nonempty
  · set m : ℝ := I.inf' hIne
        (fun i => P.bR i - inner ℝ (P.nR i) (P.posR f + s₀ • (x - P.posR f))) with hm
    set M : ℝ := I.sup' hIne
        (fun i => |inner ℝ (P.nR i) (x - P.posR f)|) with hM
    have hm_pos : 0 < m := by
      rw [hm, Finset.lt_inf'_iff hIne]
      intro i hiI
      have hi : i ∉ P.tight f := (hImem i).mp hiI
      have := hstrict i hi
      linarith
    have hM_nonneg : 0 ≤ M := by
      obtain ⟨i₀, hi₀⟩ := hIne.exists_mem
      rw [hM]
      have hle := Finset.le_sup' (s := I)
        (f := fun i => |inner ℝ (P.nR i) (x - P.posR f)|) hi₀
      linarith [abs_nonneg (inner ℝ (P.nR i₀) (x - P.posR f))]
    refine ⟨m / (M + 1), div_pos hm_pos (by linarith), ?_⟩
    rw [mem_Pset_iff]
    intro i
    by_cases hi : i ∈ P.tight f
    · rw [ray_tight_basic P h f hx hi]
    · have hiI : i ∈ I := (hImem i).mpr hi
      have hmi : m ≤ P.bR i - inner ℝ (P.nR i) (P.posR f + s₀ • (x - P.posR f)) := by
        rw [hm]; exact Finset.inf'_le _ hiI
      have hMi : |inner ℝ (P.nR i) (x - P.posR f)| ≤ M := by
        rw [hM]
        exact Finset.le_sup' (s := I) (f := fun i => |inner ℝ (P.nR i) (x - P.posR f)|) hiI
      have hkey : inner ℝ (P.nR i) (P.posR f + (s₀ + m / (M + 1)) • (x - P.posR f))
          = inner ℝ (P.nR i) (P.posR f + s₀ • (x - P.posR f))
            + (m / (M + 1)) * inner ℝ (P.nR i) (x - P.posR f) := by
        rw [add_smul, ← add_assoc, inner_add_right, inner_smul_right]
      rw [hkey]
      have h3 : (m / (M + 1)) * M ≤ m := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : (0:ℝ) < M + 1)]
        nlinarith [hm_pos.le]
      have hδ : (0:ℝ) ≤ m / (M + 1) := le_of_lt (div_pos hm_pos (by linarith))
      calc inner ℝ (P.nR i) (P.posR f + s₀ • (x - P.posR f))
              + (m / (M + 1)) * inner ℝ (P.nR i) (x - P.posR f)
          ≤ inner ℝ (P.nR i) (P.posR f + s₀ • (x - P.posR f))
              + (m / (M + 1)) * |inner ℝ (P.nR i) (x - P.posR f)| := by
            gcongr; exact le_abs_self _
        _ ≤ inner ℝ (P.nR i) (P.posR f + s₀ • (x - P.posR f)) + (m / (M + 1)) * M := by
            gcongr
        _ ≤ P.bR i := by linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hIne
    refine ⟨1, one_pos, ?_⟩
    rw [mem_Pset_iff]
    intro i
    have hi : i ∈ P.tight f := by
      by_contra hc
      have : i ∈ I := (hImem i).mpr hc
      rw [hIne] at this
      exact Finset.notMem_empty i this
    rw [ray_tight_basic P h f hx hi]

/-! ### The exit lemma -/

/-- Radial exit lemma, from the basic checks only. For a point `x` of the face `Fset f` which lies
in its relative interior (in the sense that its tight set is exactly `tight f`), the ray from
`posR f` through `x` leaves the polytope at a parameter `t > 1`; `t` is the greatest parameter of
the ray that stays in `Pset`, the exit point `r` is in the face, and a new constraint becomes tight
there. -/
theorem exists_exit_basic {d : ℕ} (P : Work.ConvexCells.PolytopeData d) (h : P.OkBasic) (f : Fin P.K)
    {x : Work.ConvexCells.E d} (hx : x ∈ P.Fset f) (hxt : P.tightAt x = P.tight f)
    (hne : x ≠ P.posR f) :
    ∃ (t : ℝ) (r : Work.ConvexCells.E d), 1 < t ∧ r = P.posR f + t • (x - P.posR f) ∧
      r ∈ P.Fset f ∧ P.tight f ⊂ P.tightAt r ∧ x = (1 - t⁻¹) • P.posR f + t⁻¹ • r ∧
      (∀ s : ℝ, 0 ≤ s → s ≤ t → P.posR f + s • (x - P.posR f) ∈ P.Pset) ∧
      (∀ s : ℝ, t < s → P.posR f + s • (x - P.posR f) ∉ P.Pset) := by
  have hvne : x - P.posR f ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
  obtain ⟨R, hR⟩ := Pset_bounded_basic P h
  set A : Set ℝ := {s | 0 ≤ s ∧ P.posR f + s • (x - P.posR f) ∈ P.Pset} with hA
  have hcont : Continuous (fun s : ℝ => P.posR f + s • (x - P.posR f)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hAclosed : IsClosed A := by
    have hE : A = Set.Ici 0 ∩ (fun s : ℝ => P.posR f + s • (x - P.posR f)) ⁻¹' P.Pset := by
      rw [hA]; ext s; simp [Set.mem_Ici]
    rw [hE]
    exact isClosed_Ici.inter (P.Pset_isClosed.preimage hcont)
  have h0A : (0:ℝ) ∈ A := by
    rw [hA]
    exact ⟨le_refl 0, by simpa using Work.ConvexCells.posR_mem_Pset_basic h f⟩
  have h1A : (1:ℝ) ∈ A := by
    rw [hA]
    refine ⟨zero_le_one, ?_⟩
    have he : P.posR f + (1:ℝ) • (x - P.posR f) = x := by rw [one_smul, add_sub_cancel]
    rw [he]; exact hx.1
  have hAbdd : BddAbove A := by
    refine ⟨(R + ‖P.posR f‖) / ‖x - P.posR f‖, ?_⟩
    intro s hs
    rw [hA] at hs
    have h1 : ‖s • (x - P.posR f)‖ ≤ R + ‖P.posR f‖ := by
      have h2 := hR hs.2
      rw [Metric.mem_closedBall, dist_zero_right] at h2
      have h3 : ‖s • (x - P.posR f)‖ = ‖(P.posR f + s • (x - P.posR f)) - P.posR f‖ := by
        congr 1; abel
      rw [h3]
      exact le_trans (norm_sub_le _ _) (by linarith)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1] at h1
    rw [le_div_iff₀ (norm_pos_iff.mpr hvne)]
    linarith
  set T : ℝ := sSup A with hT
  have hTmem : T ∈ A := by
    rw [hT]; exact hAclosed.csSup_mem ⟨0, h0A⟩ hAbdd
  have hTub : ∀ s ∈ A, s ≤ T := by
    intro s hs; rw [hT]; exact le_csSup hAbdd hs
  have hTge1 : 1 ≤ T := hTub 1 h1A
  have hTpos : 0 < T := by linarith
  have hstrict1 : ∀ i, i ∉ P.tight f →
      inner ℝ (P.nR i) (P.posR f + (1:ℝ) • (x - P.posR f)) < P.bR i := by
    intro i hi
    have heq : P.posR f + (1:ℝ) • (x - P.posR f) = x := by rw [one_smul, add_sub_cancel]
    rw [heq]
    have hni : i ∉ P.tightAt x := by rw [hxt]; exact hi
    exact not_le.mp (fun hh => hni ((mem_tightAt_iff P x i).mpr hh))
  obtain ⟨δ, hδpos, hδmem⟩ := ray_extends_basic P h f hx (1:ℝ) hstrict1
  have h1δA : (1 + δ) ∈ A := by
    rw [hA]; exact ⟨by linarith, hδmem⟩
  have hTgt1 : 1 < T := by
    have := hTub (1 + δ) h1δA; linarith
  have hTPset : P.posR f + T • (x - P.posR f) ∈ P.Pset := by
    have hmm := hTmem; rw [hA] at hmm; exact hmm.2
  have hTF : P.posR f + T • (x - P.posR f) ∈ P.Fset f :=
    ⟨hTPset, fun i hi => ray_tight_basic P h f hx hi T⟩
  have hTnotmem : ∀ s : ℝ, T < s → P.posR f + s • (x - P.posR f) ∉ P.Pset := by
    intro s hs hmem
    have hsA : s ∈ A := by rw [hA]; exact ⟨by linarith, hmem⟩
    have := hTub s hsA; linarith
  have hmemIcc : ∀ s : ℝ, 0 ≤ s → s ≤ T → P.posR f + s • (x - P.posR f) ∈ P.Pset := by
    intro s hs0 hsT
    have hTne : T ≠ 0 := ne_of_gt hTpos
    have hsplit : P.posR f + s • (x - P.posR f)
        = (1 - s/T) • (P.posR f + (0:ℝ) • (x - P.posR f))
          + (s/T) • (P.posR f + T • (x - P.posR f)) := by
      rw [show (P.posR f + (0:ℝ) • (x - P.posR f)) = P.posR f by rw [zero_smul, _root_.add_zero]]
      rw [show (s/T) • (P.posR f + T • (x - P.posR f))
            = (s/T) • P.posR f + s • (x - P.posR f) by
          rw [smul_add, smul_smul, div_mul_cancel₀ s hTne]]
      rw [← add_assoc, ← add_smul, show 1 - s/T + s/T = 1 by ring, one_smul]
    rw [hsplit]
    refine P.Pset_convex (by rw [zero_smul, _root_.add_zero]; exact Work.ConvexCells.posR_mem_Pset_basic h f)
      hTPset ?_ ?_ ?_
    · exact sub_nonneg.mpr (by rw [div_le_one hTpos]; exact hsT)
    · exact div_nonneg hs0 hTpos.le
    · ring
  have hsub : P.tight f ⊆ P.tightAt (P.posR f + T • (x - P.posR f)) := by
    intro i hi
    rw [mem_tightAt_iff, ray_tight_basic P h f hx hi T]
  have hneT : P.tight f ≠ P.tightAt (P.posR f + T • (x - P.posR f)) := by
    intro heq
    have hstrictT : ∀ i, i ∉ P.tight f →
        inner ℝ (P.nR i) (P.posR f + T • (x - P.posR f)) < P.bR i := by
      intro i hi
      have hni : i ∉ P.tightAt (P.posR f + T • (x - P.posR f)) := by rw [← heq]; exact hi
      exact not_le.mp (fun hh => hni ((mem_tightAt_iff P _ i).mpr hh))
    obtain ⟨δ', hδ'pos, hδ'mem⟩ := ray_extends_basic P h f hx T hstrictT
    have : T + δ' ∈ A := by rw [hA]; exact ⟨by linarith, hδ'mem⟩
    have := hTub (T + δ') this
    linarith
  refine ⟨T, P.posR f + T • (x - P.posR f), hTgt1, rfl, hTF,
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hneT⟩, ?_, hmemIcc, hTnotmem⟩
  rw [smul_add, smul_smul, inv_mul_cancel₀ (ne_of_gt hTpos), one_smul, ← add_assoc, ← add_smul,
    show (1 - T⁻¹) + T⁻¹ = 1 by ring, one_smul]
  abel

end Work.MbarHomology.ConvexCells
