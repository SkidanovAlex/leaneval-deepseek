import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.MinkDefs

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Q44Geom

open Work.HP

/-- `eNorm` of an integer multiple: `‖c • v‖ = |c| · ‖v‖`. -/
lemma eNorm_zsmul_int {ι : Type*} [Fintype ι] (c : ℤ) (v : ι → ℤ) :
    Work.HP.eNorm (c • v) = |(c : ℝ)| * Work.HP.eNorm v := by
  rw [Work.HP.eNorm, Work.HP.eNorm]
  have hsum : (∑ i, (((c • v) i : ℤ) : ℝ) ^ 2)
      = (c : ℝ) ^ 2 * ∑ i, ((v i : ℤ) : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast; ring
  rw [hsum, Real.sqrt_mul (sq_nonneg (c : ℝ)), Real.sqrt_sq_eq_abs]

/-- In a rank-two sublattice of `ℤ^ι`, a shortest non-zero vector can be completed to a
generating pair. -/
theorem exists_completion_of_shortest {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : Submodule ℤ (ι → ℤ)) (hN : Work.HP.rk N = 2) (x : ι → ℤ) (hxN : x ∈ N) (hx0 : x ≠ 0)
    (hmin : ∀ v ∈ N, v ≠ 0 → Work.HP.eNorm x ≤ Work.HP.eNorm v) :
    ∃ w : ι → ℤ, w ∈ N ∧ N = Submodule.span ℤ ({x, w} : Set (ι → ℤ)) := by
  classical
  -- ## Step 1: minimality makes `x` primitive (not a non-trivial multiple inside `N`).
  have hprim : ∀ (m : ℤ) (y : ι → ℤ), y ∈ N → x = m • y → m.natAbs = 1 := by
    intro m y hyN hxy
    have hy0 : y ≠ 0 := by
      rintro rfl; rw [smul_zero] at hxy; exact hx0 hxy
    have hle := hmin y hyN hy0
    have hnorm : Work.HP.eNorm x = |(m : ℝ)| * Work.HP.eNorm y := by
      rw [hxy, eNorm_zsmul_int]
    have hypos : 0 < Work.HP.eNorm y := Work.HP.eNorm_pos_of_ne_zero hy0
    rw [hnorm] at hle
    have habs : |(m : ℝ)| ≤ 1 := by
      refine le_of_mul_le_mul_right (b := |(m:ℝ)|) (c := 1) ?_ hypos
      simpa using hle
    have hmne : m ≠ 0 := by
      rintro rfl; simp only [zero_smul] at hxy; exact hx0 hxy
    have hcast : |(m : ℝ)| = (m.natAbs : ℝ) := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]
      exact Int.cast_natCast _
    rw [hcast] at habs
    have h1 : 1 ≤ m.natAbs := by
      have := Int.natAbs_pos.mpr hmne; omega
    have h2 : m.natAbs ≤ 1 := by exact_mod_cast habs
    omega
  -- ## Step 2: a `ℤ`-basis of `N`, which has rank `2`.
  obtain ⟨n, B⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) N
  have hn : n = 2 := by
    rw [show n = Module.finrank ℤ N from by rw [Module.finrank_eq_card_basis B]; simp]
    rw [← hN]; rfl
  subst hn
  have hspanB : N = Submodule.span ℤ (Set.range fun i : Fin 2 => (B i : ι → ℤ)) := by
    have key : Submodule.map N.subtype (Submodule.span ℤ (Set.range B))
        = Submodule.span ℤ (Set.range fun i : Fin 2 => (B i : ι → ℤ)) := by
      rw [Submodule.map_span]
      congr 1
      rw [← Set.range_comp]; rfl
    have key2 : Submodule.map N.subtype (Submodule.span ℤ (Set.range B)) = N := by
      rw [Module.Basis.span_eq B, Submodule.map_top, Submodule.range_subtype]
    exact key2.symm.trans key
  -- ## Step 3: coordinates of `x` in the basis `B`.
  let xN : N := ⟨x, hxN⟩
  let a : ℤ := B.repr xN 0
  let b : ℤ := B.repr xN 1
  have hxrepr : a • B 0 + b • B 1 = xN := by
    rw [← B.sum_repr xN, Fin.sum_univ_two]
  have hx_amb : a • (B 0 : ι → ℤ) + b • (B 1 : ι → ℤ) = x := by
    have := congrArg Subtype.val hxrepr
    simpa using this
  have hxN0 : xN ≠ 0 := by
    intro h
    apply hx0
    have := congrArg Subtype.val h
    simpa [xN] using this
  -- ## Step 4: `gcd a b = 1`, by primitivity of `x`.
  have hcoef : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    have hz : a • B 0 + b • B 1 = (0 : N) := by rw [h.1, h.2]; simp
    rw [hz] at hxrepr
    exact hxN0 hxrepr.symm
  have hgcd : a.gcd b = 1 := by
    by_contra hg
    have hpos : 0 < a.gcd b := by
      rcases hcoef with h | h
      · exact Int.gcd_pos_of_ne_zero_left b h
      · exact Int.gcd_pos_of_ne_zero_right a h
    have hge : 2 ≤ a.gcd b := by omega
    obtain ⟨a', ha'⟩ := (Int.gcd_dvd_left a b : ((a.gcd b : ℕ) : ℤ) ∣ a)
    obtain ⟨b', hb'⟩ := (Int.gcd_dvd_right a b : ((a.gcd b : ℕ) : ℤ) ∣ b)
    let yN : N := a' • B 0 + b' • B 1
    have hgy : ((a.gcd b : ℕ) : ℤ) • yN = xN := by
      show ((a.gcd b : ℕ) : ℤ) • (a' • B 0 + b' • B 1) = xN
      rw [smul_add, smul_smul, smul_smul, ← ha', ← hb']
      exact hxrepr
    have hgy_amb : ((a.gcd b : ℕ) : ℤ) • (yN : ι → ℤ) = x := by
      have := congrArg Subtype.val hgy
      simpa using this
    have hgenat : (((a.gcd b : ℕ) : ℤ)).natAbs = 1 :=
      hprim _ (yN : ι → ℤ) yN.2 hgy_amb.symm
    rw [Int.natAbs_natCast] at hgenat
    omega
  -- ## Step 5: Bézout coefficients give a unimodular companion.
  have hbez : a * a.gcdA b + b * a.gcdB b = 1 := by
    have h := Int.gcd_eq_gcd_ab a b
    rw [hgcd] at h
    norm_num at h
    exact h.symm
  let c : ℤ := -(a.gcdB b)
  let d : ℤ := a.gcdA b
  have hdet : a * d - b * c = 1 := by
    have h : a * d - b * c = a * a.gcdA b + b * a.gcdB b := by
      simp only [c, d]; ring
    rw [h, hbez]
  -- ## Step 6: the companion `w`.
  let wN : N := c • B 0 + d • B 1
  let w : ι → ℤ := (wN : ι → ℤ)
  have hw_amb : c • (B 0 : ι → ℤ) + d • (B 1 : ι → ℤ) = w := rfl
  refine ⟨w, wN.2, ?_⟩
  apply le_antisymm
  · -- `N ≤ span {x, w}`: the basis vectors are integral combinations of `x` and `w`.
    rw [hspanB, Submodule.span_le]
    intro v hv
    rcases hv with ⟨i, rfl⟩
    have hxs : x ∈ Submodule.span ℤ ({x, w} : Set (ι → ℤ)) :=
      Submodule.subset_span (by simp)
    have hws : w ∈ Submodule.span ℤ ({x, w} : Set (ι → ℤ)) :=
      Submodule.subset_span (by simp)
    fin_cases i
    · change (B 0 : ι → ℤ) ∈ Submodule.span ℤ ({x, w} : Set (ι → ℤ))
      have hB0 : (B 0 : ι → ℤ) = d • x - b • w := by
        rw [← hx_amb, ← hw_amb]
        have hdet' : d * a - b * c = 1 := by rw [mul_comm d a]; exact hdet
        have h : d • (a • (B 0 : ι → ℤ) + b • (B 1 : ι → ℤ))
              - b • (c • (B 0 : ι → ℤ) + d • (B 1 : ι → ℤ))
            = (d*a - b*c) • (B 0 : ι → ℤ) + (d*b - b*d) • (B 1 : ι → ℤ) := by
          module
        rw [h, hdet', show d*b - b*d = 0 by ring, zero_smul, add_zero, one_smul]
      rw [hB0]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ d hxs) (Submodule.smul_mem _ b hws)
    · change (B 1 : ι → ℤ) ∈ Submodule.span ℤ ({x, w} : Set (ι → ℤ))
      have hB1 : (B 1 : ι → ℤ) = -c • x + a • w := by
        rw [← hx_amb, ← hw_amb]
        have hdet'' : a * d - c * b = 1 := by rw [mul_comm c b]; exact hdet
        have h : - c • (a • (B 0 : ι → ℤ) + b • (B 1 : ι → ℤ))
              + a • (c • (B 0 : ι → ℤ) + d • (B 1 : ι → ℤ))
            = (a*c - c*a) • (B 0 : ι → ℤ) + (a*d - c*b) • (B 1 : ι → ℤ) := by
          module
        rw [h, show a*c - c*a = 0 by ring, zero_smul, zero_add, hdet'', one_smul]
      rw [hB1]
      exact Submodule.add_mem _ (Submodule.smul_mem _ (-c) hxs) (Submodule.smul_mem _ a hws)
  · -- `span {x, w} ≤ N`
    rw [Submodule.span_le]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact hxN
    · exact wN.2

end Work.Q44Geom
