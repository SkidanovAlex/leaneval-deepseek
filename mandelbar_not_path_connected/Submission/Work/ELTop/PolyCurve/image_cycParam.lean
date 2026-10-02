import Mathlib
import Submission.Work.ELTop.PolyCurve.Defs
import Submission.Work.ELTop.PolyCurve.notInArc_iff_exists_Icc
import Submission.Work.ELTop.rayPiece_eq_image
import Submission.Work.ELTop.PolyCurve.Blocks
import Submission.Work.ELTop.PolyCurve.rayArc_facts
import Submission.Work.ELTop.PolyCurve.eqArcPt_facts
import Submission.Work.ELTop.PolyCurve.Inject

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.ELTop.PolyCurve

variable {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}

/-! ## Shifting the external angle by an integer -/

/-- `InArc` only depends on the angles modulo `1`: shifting both endpoints of the arc by the
same integer does not change membership. -/
theorem InArc_add_int_pair (θ a b : ℝ) (n : ℤ) :
    Work.EL.InArc θ (a + (n : ℝ)) (b + (n : ℝ)) ↔ Work.EL.InArc θ a b := by
  unfold Work.EL.InArc Work.EL.arcLen
  have h1 : Int.fract (θ - (a + (n : ℝ))) = Int.fract (θ - a) := by
    have h : θ - (a + (n : ℝ)) = (θ - a) - (n : ℝ) := by ring
    rw [h, Int.fract_sub_intCast]
  have h2 : Int.fract ((b + (n : ℝ)) - (a + (n : ℝ))) = Int.fract (b - a) := by
    have h : (b + (n : ℝ)) - (a + (n : ℝ)) = b - a := by ring
    rw [h]
  rw [h1, h2]

/-- `InArc` only depends on the point modulo `1`: shifting `θ` by an integer does not change
membership. -/
theorem InArc_add_int_angle (θ a b : ℝ) (n : ℤ) :
    Work.EL.InArc (θ + (n : ℝ)) a b ↔ Work.EL.InArc θ a b := by
  unfold Work.EL.InArc Work.EL.arcLen
  have h1 : Int.fract ((θ + (n : ℝ)) - a) = Int.fract (θ - a) := by
    have h : (θ + (n : ℝ)) - a = (θ - a) + (n : ℝ) := by ring
    rw [h, Int.fract_add_intCast]
  rw [h1]

/-! ## The angle data of a matching lift -/

theorem matches_m {D : CycLift hN} {ps : List (Work.EL.CoPair hN)} (hM : D.Matches ps) :
    D.m = ps.length := hM.1

/-- At a natural-number index the lift `A` reproduces the first angle of `ps`. -/
theorem matches_A {D : CycLift hN} {ps : List (Work.EL.CoPair hN)} (hM : D.Matches ps)
    (i : Fin ps.length) : D.A (i : ℤ) = (ps.get i).a := by
  obtain ⟨k, q, hk, hA, -, -⟩ := hM.2 i
  have hlenZ : ((ps.length : ℕ) : ℤ) = ((D.m : ℕ) : ℤ) := by rw [hM.1]
  have hAadd : ∀ t : ℤ, D.A (t + (ps.length : ℤ)) = D.A t + 1 := by
    intro t
    rw [hlenZ]
    exact D.A_add t
  have hk' : (i : ℤ) = k + (ps.length : ℤ) * (-q) := by
    rw [hk]; ring
  have hs : D.A (k + (ps.length : ℤ) * (-q)) = D.A k + ((-q : ℤ) : ℝ) :=
    shift_of_add hAadd k (-q)
  rw [← hk'] at hs
  have hq' : (((-q : ℤ)) : ℝ) = -(q : ℝ) := by push_cast; ring
  linarith [hs, hA, hq']

/-- At a natural-number index the lift `B` reproduces the second angle of `ps`. -/
theorem matches_B {D : CycLift hN} {ps : List (Work.EL.CoPair hN)} (hM : D.Matches ps)
    (i : Fin ps.length) : D.B (i : ℤ) = (ps.get i).b := by
  obtain ⟨k, q, hk, -, hB, -⟩ := hM.2 i
  have hlenZ : ((ps.length : ℕ) : ℤ) = ((D.m : ℕ) : ℤ) := by rw [hM.1]
  have hBadd : ∀ t : ℤ, D.B (t + (ps.length : ℤ)) = D.B t + 1 := by
    intro t
    rw [hlenZ]
    exact D.B_add t
  have hk' : (i : ℤ) = k + (ps.length : ℤ) * (-q) := by
    rw [hk]; ring
  have hs : D.B (k + (ps.length : ℤ) * (-q)) = D.B k + ((-q : ℤ) : ℝ) :=
    shift_of_add hBadd k (-q)
  rw [← hk'] at hs
  have hq' : (((-q : ℤ)) : ℝ) = -(q : ℝ) := by push_cast; ring
  linarith [hs, hB, hq']

/-- At a natural-number index the lift `Y` reproduces the landing point of `ps`. -/
theorem matches_Y {D : CycLift hN} {ps : List (Work.EL.CoPair hN)} (hM : D.Matches ps)
    (i : Fin ps.length) : D.Y (i : ℤ) = (ps.get i).y := by
  obtain ⟨k, q, hk, -, -, hY⟩ := hM.2 i
  have hlenZ : ((ps.length : ℕ) : ℤ) = ((D.m : ℕ) : ℤ) := by rw [hM.1]
  have hYadd : ∀ t : ℤ, D.Y (t + (ps.length : ℤ)) = D.Y t := by
    intro t
    rw [hlenZ]
    exact D.Y_add t
  have hYsub : ∀ t : ℤ, D.Y (t - (ps.length : ℤ)) = D.Y t := by
    intro t
    rw [hlenZ]
    exact D.Y_sub_m t
  have hYshift : ∀ (r : ℤ), D.Y (k + (ps.length : ℤ) * r) = D.Y k := by
    intro r
    induction r using Int.induction_on with
    | zero => simp
    | succ n ih =>
        have h1 : k + (ps.length : ℤ) * ((n : ℤ) + 1)
            = (k + (ps.length : ℤ) * (n : ℤ)) + (ps.length : ℤ) := by ring
        rw [h1, hYadd, ih]
    | pred n ih =>
        have h1 : k + (ps.length : ℤ) * (-(n : ℤ) - 1)
            = (k + (ps.length : ℤ) * (-(n : ℤ))) - (ps.length : ℤ) := by ring
        rw [h1, hYsub, ih]
  have hk' : (i : ℤ) = k + (ps.length : ℤ) * (-q) := by
    rw [hk]; ring
  have hs : D.Y (k + (ps.length : ℤ) * (-q)) = D.Y k := hYshift (-q)
  rw [← hk'] at hs
  rw [hs, hY]

/-- At *any* integer index, the pair `(D.A k, D.B k)` of the lift is one of the pairs of `ps`,
up to an integer shift of both angles, with the matching landing point. -/
theorem matches_angle {D : CycLift hN} {ps : List (Work.EL.CoPair hN)} (hM : D.Matches ps)
    (k : ℤ) :
    ∃ P ∈ ps, ∃ q : ℤ, D.A k = P.a + (q : ℝ) ∧ D.B k = P.b + (q : ℝ) ∧ D.Y k = P.y := by
  have hm0 : (D.m : ℤ) ≠ 0 := by
    have := D.m_pos; omega
  have hmpos : (0 : ℤ) < (D.m : ℤ) := by
    have := D.m_pos; omega
  have hj0 : 0 ≤ k % (D.m : ℤ) := Int.emod_nonneg k hm0
  have hjm : k % (D.m : ℤ) < (D.m : ℤ) := Int.emod_lt_of_pos k hmpos
  let i : Fin ps.length := ⟨(k % (D.m : ℤ)).toNat, by
    rw [← hM.1]
    exact (Int.toNat_lt hj0).mpr hjm⟩
  have hi : ((i : ℕ) : ℤ) = k % (D.m : ℤ) := Int.toNat_of_nonneg hj0
  have hkm : k = (D.m : ℤ) * (k / (D.m : ℤ)) + k % (D.m : ℤ) :=
    (Int.mul_ediv_add_emod k (D.m : ℤ)).symm
  have hkD : k = ((i : ℕ) : ℤ) + (D.m : ℤ) * (k / (D.m : ℤ)) := by
    linarith [hkm, hi]
  refine ⟨ps.get i, List.get_mem _ _, k / (D.m : ℤ), ?_, ?_, ?_⟩
  · have h1 : D.A k = D.A ((i : ℕ) : ℤ) + (((k / (D.m : ℤ)) : ℤ) : ℝ) := by
      conv_lhs => rw [hkD]
      exact D.A_shift ((i : ℕ) : ℤ) (k / (D.m : ℤ))
    rw [h1, matches_A hM i]
  · have h1 : D.B k = D.B ((i : ℕ) : ℤ) + (((k / (D.m : ℤ)) : ℤ) : ℝ) := by
      conv_lhs => rw [hkD]
      exact D.B_shift ((i : ℕ) : ℤ) (k / (D.m : ℤ))
    rw [h1, matches_B hM i]
  · have h1 : D.Y k = D.Y ((i : ℕ) : ℤ) := by
      conv_lhs => rw [hkD]
      exact D.Y_shift ((i : ℕ) : ℤ) (k / (D.m : ℤ))
    rw [h1, matches_Y hM i]

/-- The ray of angle `D.A k` lands at `D.Y k`. -/
theorem matches_lands_A {D : CycLift hN} {ps : List (Work.EL.CoPair hN)} (hM : D.Matches ps)
    (k : ℤ) : Work.EL.LandsN hN (D.A k) (D.Y k) := by
  obtain ⟨P, hP, q, hA, -, hY⟩ := matches_angle hM k
  rw [hA, hY]
  exact Work.ELTop.LandsN_add_int hN P.lands_a q

/-- The ray of angle `D.B k` lands at `D.Y k`. -/
theorem matches_lands_B {D : CycLift hN} {ps : List (Work.EL.CoPair hN)} (hM : D.Matches ps)
    (k : ℤ) : Work.EL.LandsN hN (D.B k) (D.Y k) := by
  obtain ⟨P, hP, q, -, hB, hY⟩ := matches_angle hM k
  rw [hB, hY]
  exact Work.ELTop.LandsN_add_int hN P.lands_b q

/-- The angles `θ` which are not in any of the arcs of the pairs of `ps` are exactly those in
one of the complementary arcs `[D.B k, D.A (k+1)]` of the lift. -/
theorem matches_notInArc_iff {D : CycLift hN} {ps : List (Work.EL.CoPair hN)} (hM : D.Matches ps)
    (θ : ℝ) :
    (∀ P ∈ ps, ¬ Work.EL.InArc θ P.a P.b) ↔ ∃ k : ℤ, D.B k ≤ θ ∧ θ ≤ D.A (k + 1) := by
  rw [← notInArc_iff_exists_Icc D.hm D.A_add D.B_add D.A_lt_B D.B_lt_A θ]
  constructor
  · intro h k
    obtain ⟨P, hP, q, hA, hB, -⟩ := matches_angle hM k
    rw [hA, hB]
    exact fun hin => h P hP ((InArc_add_int_pair θ P.a P.b q).mp hin)
  · intro h P hP
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hP
    rw [← matches_A hM i, ← matches_B hM i]
    exact h i

/-- For every pair of `ps` there is a block index `k ∈ [1-m, 0]` carrying its first angle (up
to an integer shift) and its landing point. -/
theorem matches_block_a {D : CycLift hN} {ps : List (Work.EL.CoPair hN)} (hM : D.Matches ps)
    (i : Fin ps.length) :
    ∃ k : ℤ, ∃ q : ℤ, 1 - (D.m : ℤ) ≤ k ∧ k ≤ 0 ∧
      D.A k = (ps.get i).a + (q : ℝ) ∧ D.Y k = (ps.get i).y := by
  have hm1 : (1 : ℤ) ≤ (D.m : ℤ) := by
    have := D.m_pos; omega
  have him : (i : ℤ) < (D.m : ℤ) := by
    have h1 : ((i : ℕ) : ℤ) < ((ps.length : ℕ) : ℤ) := by exact_mod_cast i.isLt
    have h2 : ((ps.length : ℕ) : ℤ) = ((D.m : ℕ) : ℤ) := by rw [hM.1]
    have h3 : ((i : ℕ) : ℤ) < ((D.m : ℕ) : ℤ) := by omega
    exact h3
  rcases eq_or_ne (i : ℕ) 0 with hi0 | hi0
  · have hiz : (i : ℤ) = 0 := by
      have : ((i : ℕ) : ℤ) = 0 := by simp [hi0]
      exact this
    refine ⟨0, 0, by omega, le_refl 0, ?_, ?_⟩
    · have h := matches_A hM i
      rw [hiz] at h
      simpa using h
    · have h := matches_Y hM i
      rw [hiz] at h
      simpa using h
  · have hi1 : (1 : ℤ) ≤ (i : ℤ) := by
      have hpos : 0 < (i : ℕ) := Nat.pos_of_ne_zero hi0
      have : (1 : ℤ) ≤ ((i : ℕ) : ℤ) := by omega
      exact this
    refine ⟨(i : ℤ) - (D.m : ℤ), -1, by omega, by omega, ?_, ?_⟩
    · have hk : (i : ℤ) - (D.m : ℤ) = (i : ℤ) + (D.m : ℤ) * (-1) := by ring
      rw [hk, D.A_shift (i : ℤ) (-1), matches_A hM i]
    · have hk : (i : ℤ) - (D.m : ℤ) = (i : ℤ) + (D.m : ℤ) * (-1) := by ring
      rw [hk, D.Y_shift (i : ℤ) (-1), matches_Y hM i]

/-- For every pair of `ps` there is a block index `κ ∈ [1-m, 0]` whose *second* ray carries the
second angle of the pair (up to an integer shift), with the matching landing point. -/
theorem matches_block_b {D : CycLift hN} {ps : List (Work.EL.CoPair hN)} (hM : D.Matches ps)
    (i : Fin ps.length) :
    ∃ κ : ℤ, ∃ q : ℤ, 1 - (D.m : ℤ) ≤ κ ∧ κ ≤ 0 ∧
      D.B (κ - 1) = (ps.get i).b + (q : ℝ) ∧ D.Y (κ - 1) = (ps.get i).y := by
  have hm1 : (1 : ℤ) ≤ (D.m : ℤ) := by
    have := D.m_pos; omega
  have hi0 : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg _
  have him : (i : ℤ) < (D.m : ℤ) := by
    have h1 : ((i : ℕ) : ℤ) < ((ps.length : ℕ) : ℤ) := by exact_mod_cast i.isLt
    have h2 : ((ps.length : ℕ) : ℤ) = ((D.m : ℕ) : ℤ) := by rw [hM.1]
    have h3 : ((i : ℕ) : ℤ) < ((D.m : ℕ) : ℤ) := by omega
    exact h3
  refine ⟨(i : ℤ) + 1 - (D.m : ℤ), -1, by omega, by omega, ?_, ?_⟩
  · have hk : (i : ℤ) + 1 - (D.m : ℤ) - 1 = (i : ℤ) + (D.m : ℤ) * (-1) := by ring
    rw [hk, D.B_shift (i : ℤ) (-1), matches_B hM i]
  · have hk : (i : ℤ) + 1 - (D.m : ℤ) - 1 = (i : ℤ) + (D.m : ℤ) * (-1) := by ring
    rw [hk, D.Y_shift (i : ℤ) (-1), matches_Y hM i]

/-! ## The angles of a block window avoid the pair arcs -/

theorem notInArc_of_block_window {D : CycLift hN} {ps : List (Work.EL.CoPair hN)}
    (hM : D.Matches ps) {κ : ℤ} {θ : ℝ}
    (hθ : θ ∈ Set.Icc (D.B (κ - 1)) (D.A κ)) :
    ∀ P ∈ ps, ¬ Work.EL.InArc θ P.a P.b := by
  rw [matches_notInArc_iff hM]
  refine ⟨κ - 1, hθ.1, ?_⟩
  have h : (κ - 1) + 1 = κ := by ring
  rw [h]
  exact hθ.2

/-! ## Shifting into the fundamental domain and back -/

/-- Every real is an integer translate of a point of `[0,1]`. -/
theorem exists_Icc_add_int (θ : ℝ) : ∃ θ' ∈ Set.Icc (0 : ℝ) 1, ∃ n : ℤ, θ' = θ + n := by
  refine ⟨θ - ⌊θ⌋, ⟨?_, ?_⟩, -⌊θ⌋, ?_⟩
  · have h2 : θ - ⌊θ⌋ = Int.fract θ := by linarith [Int.fract_add_floor θ]
    rw [h2]
    exact Int.fract_nonneg θ
  · have h2 : θ - ⌊θ⌋ = Int.fract θ := by linarith [Int.fract_add_floor θ]
    rw [h2]
    exact le_of_lt (Int.fract_lt_one θ)
  · push_cast
    ring

/-- Every complementary arc `[D.B j, D.A (j+1)]` of the lift is an integer translate of one of
the `m` complementary arcs `[D.B (κ-1), D.A κ]` with block index `κ ∈ [1-m, 0]`. -/
theorem exists_block_interval (D : CycLift hN) (j : ℤ) :
    ∃ κ : ℤ, 1 - (D.m : ℤ) ≤ κ ∧ κ ≤ 0 ∧ ∃ n : ℤ,
      D.A κ = D.A (j + 1) + (n : ℝ) ∧ D.B (κ - 1) = D.B j + (n : ℝ) := by
  have hm : (0 : ℤ) < (D.m : ℤ) := by
    have := D.m_pos; omega
  have hm0 : (D.m : ℤ) ≠ 0 := ne_of_gt hm
  set q : ℤ := (j + 1) / (D.m : ℤ) with hq
  set r : ℤ := (j + 1) % (D.m : ℤ) with hr
  have hr0 : 0 ≤ r := by rw [hr]; exact Int.emod_nonneg _ hm0
  have hrm : r < (D.m : ℤ) := by rw [hr]; exact Int.emod_lt_of_pos _ hm
  have hjr : j = (D.m : ℤ) * q + r - 1 := by
    have h1 := Int.mul_ediv_add_emod (j + 1) (D.m : ℤ)
    rw [← hq, ← hr] at h1
    omega
  by_cases hrz : r = 0
  · refine ⟨0, by omega, le_refl 0, -q, ?_, ?_⟩
    · have h1 : (0 : ℤ) = j + 1 + (D.m : ℤ) * (-q) := by rw [hjr, hrz]; ring
      rw [h1]; exact D.A_shift (j + 1) (-q)
    · have h1 : (0 : ℤ) - 1 = j + (D.m : ℤ) * (-q) := by rw [hjr, hrz]; ring
      rw [h1]; exact D.B_shift j (-q)
  · have hr1 : (1 : ℤ) ≤ r := by omega
    refine ⟨r - (D.m : ℤ), by omega, by omega, -q - 1, ?_, ?_⟩
    · have h1 : r - (D.m : ℤ) = j + 1 + (D.m : ℤ) * (-q - 1) := by rw [hjr]; ring
      rw [h1]; exact D.A_shift (j + 1) (-q - 1)
    · have h1 : r - (D.m : ℤ) - 1 = j + (D.m : ℤ) * (-q - 1) := by rw [hjr]; ring
      rw [h1]; exact D.B_shift j (-q - 1)

/-! ## The parameter `s = (ℓ + σ)/m` -/

/-- For `ℓ ∈ [0,m)` and `σ ∈ [0,1)` the point `s = (ℓ+σ)/m` lies in the unit interval, its
`m`-th multiple has integer part `ℓ` and fractional part `σ`. -/
theorem floor_mul_div (D : CycLift hN) {ℓ : ℤ} (hℓ0 : 0 ≤ ℓ) (hℓm : ℓ < (D.m : ℤ))
    {σ : ℝ} (hσ : σ ∈ Set.Ico 0 1) :
    ⌊(D.m : ℝ) * ((ℓ + σ) / (D.m : ℝ))⌋ = ℓ ∧
      (D.m : ℝ) * ((ℓ + σ) / (D.m : ℝ)) - (ℓ : ℝ) = σ := by
  have hmR : (0 : ℝ) < (D.m : ℝ) := by exact_mod_cast D.hm
  have h1 : (D.m : ℝ) * ((ℓ + σ) / (D.m : ℝ)) = (ℓ : ℝ) + σ := by field_simp
  constructor
  · rw [h1, Int.floor_eq_iff]
    exact ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  · rw [h1]; ring

/-- The parametrization evaluated at `s = (ℓ+σ)/m` is the block `-ℓ` at parameter `σ`. -/
theorem cycParam_at (D : CycLift hN) (R : ℝ) {ℓ : ℤ} (hℓ0 : 0 ≤ ℓ) (hℓm : ℓ < (D.m : ℤ))
    {σ : ℝ} (hσ : σ ∈ Set.Ico 0 1) :
    cycParam D R ((ℓ + σ) / (D.m : ℝ)) = cycBlock D R (-ℓ) σ := by
  obtain ⟨h1, h2⟩ := floor_mul_div D hℓ0 hℓm hσ
  unfold cycParam
  rw [h1, h2]

/-- The parametrization evaluated at `s = ℓ/m` is the initial point `D.Y (-ℓ)` of the block. -/
theorem cycParam_at_zero (D : CycLift hN) (R : ℝ) {ℓ : ℤ} (hℓ0 : 0 ≤ ℓ)
    (hℓm : ℓ < (D.m : ℤ)) :
    cycParam D R ((ℓ : ℝ) / (D.m : ℝ)) = D.Y (-ℓ) := by
  have hσ : (0 : ℝ) ∈ Set.Ico 0 1 := ⟨le_refl 0, zero_lt_one⟩
  have h := cycParam_at D R hℓ0 hℓm hσ
  have h2 : ((ℓ : ℝ) + 0) / (D.m : ℝ) = (ℓ : ℝ) / (D.m : ℝ) := by ring
  rw [h2] at h
  rw [h]
  show cycBlock D R (-ℓ) 0 = D.Y (-ℓ)
  unfold Work.ELTop.cycBlock
  rw [if_pos (by norm_num : (0 : ℝ) ≤ 1 / 3)]
  simp [Work.ELTop.rayArc]


/-! ## The middle of a block -/

theorem blkLev_mid {R u : ℝ} (hu : u ∈ Set.Icc 0 1) : blkLev R ((u + 1) / 3) = R := by
  rcases eq_or_lt_of_le hu.1 with h | h
  · have hσ : (u + 1) / 3 = 1 / 3 := by rw [← h]; ring
    rw [hσ, blkLev_branch1 (le_refl (1 / 3 : ℝ))]
    ring
  · have h1 : ¬ (u + 1) / 3 ≤ 1 / 3 := by linarith
    have h2 : (u + 1) / 3 ≤ 2 / 3 := by linarith [hu.2]
    rw [blkLev_branch2 h1 h2]

theorem blkAng_mid {hN : Work.EL.DynB c φ} (D : CycLift hN) (κ : ℤ) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1) :
    blkAng D κ ((u + 1) / 3) = D.A κ + u * (D.B (κ - 1) - D.A κ) := by
  rcases eq_or_lt_of_le hu.1 with h | h
  · have hσ : (u + 1) / 3 = 1 / 3 := by rw [← h]; ring
    rw [hσ, blkAng_branch1 (le_refl (1 / 3 : ℝ)), ← h]
    ring
  · have h1 : ¬ (u + 1) / 3 ≤ 1 / 3 := by linarith
    have h2 : (u + 1) / 3 ≤ 2 / 3 := by linarith [hu.2]
    rw [blkAng_branch2 h1 h2]
    ring

theorem blkLev_hi {R σ : ℝ} (hσ2 : 2 / 3 ≤ σ) (hσ1 : σ < 1) :
    blkLev R σ = 1 + (3 - 3 * σ) * (R - 1) := by
  rcases eq_or_lt_of_le hσ2 with h | h
  · rw [← h, blkLev_branch2 (by norm_num : ¬ (2 / 3 : ℝ) ≤ 1 / 3) le_rfl]
    ring
  · exact blkLev_branch3 (by linarith) (by linarith)

theorem blkAng_hi {hN : Work.EL.DynB c φ} (D : CycLift hN) {κ : ℤ} {σ : ℝ}
    (hσ2 : 2 / 3 ≤ σ) : blkAng D κ σ = D.B (κ - 1) := by
  rcases eq_or_lt_of_le hσ2 with h | h
  · rw [← h, blkAng_branch2 (by norm_num : ¬ (2 / 3 : ℝ) ≤ 1 / 3) le_rfl]
    ring
  · exact blkAng_branch3 (by linarith) (by linarith)

/-- `s = (ℓ + σ)/m` lies in the fundamental domain `[0,1)` whenever `0 ≤ ℓ < m` and
`0 ≤ σ ≤ 2/3`. -/
theorem mem_Ico_div {D : CycLift hN} {ℓ : ℤ} (hℓ0 : 0 ≤ ℓ) (hℓm : ℓ < (D.m : ℤ))
    {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    (ℓ + σ) / (D.m : ℝ) ∈ Set.Ico 0 1 := by
  have hmR : (0 : ℝ) < (D.m : ℝ) := by exact_mod_cast D.hm
  have hℓ0r : (0 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ0
  constructor
  · exact div_nonneg (by linarith) (le_of_lt hmR)
  · rw [div_lt_one hmR]
    have hℓm' : (ℓ : ℝ) + 1 ≤ (D.m : ℝ) := by
      have : ℓ + 1 ≤ (D.m : ℤ) := by omega
      exact_mod_cast this
    linarith

/-! ## The four pieces of the polygon are in the image of the parametrization -/

/-- The landing point of the `i`-th pair is a value of the parametrization. -/
theorem mem_image_of_y (D : CycLift hN) {ps : List (Work.EL.CoPair hN)} (hM : D.Matches ps)
    (R : ℝ) (i : Fin ps.length) : (ps.get i).y ∈ cycParam D R '' Set.Ico 0 1 := by
  obtain ⟨k, q, hk1, hk2, hA, hY⟩ := matches_block_a hM i
  set ℓ : ℤ := -k with hℓ
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; omega
  have hℓm : ℓ < (D.m : ℤ) := by rw [hℓ]; omega
  refine ⟨(ℓ : ℝ) / (D.m : ℝ), ?_, ?_⟩
  · constructor
    · exact div_nonneg (by exact_mod_cast hℓ0) (by positivity)
    · rw [div_lt_one (by exact_mod_cast D.hm)]
      exact_mod_cast hℓm
  · rw [cycParam_at_zero D R hℓ0 hℓm]
    rw [show -ℓ = k by rw [hℓ]; ring, hY]

/-- The piece of the first ray of the `i`-th pair below level `R` is in the image. -/
theorem mem_image_of_rayPiece_a (D : CycLift hN) {ps : List (Work.EL.CoPair hN)}
    (hM : D.Matches ps) {R : ℝ} (hR : 1 < R) (i : Fin ps.length) :
    ∀ z ∈ Work.EL.rayPiece hN (ps.get i).a 0 R, z ∈ cycParam D R '' Set.Ico 0 1 := by
  intro z hz
  obtain ⟨k, q, hk1, hk2, hA, hY⟩ := matches_block_a hM i
  rw [rayPiece_eq_image hN hR] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  set ℓ : ℤ := -k with hℓ
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; omega
  have hℓm : ℓ < (D.m : ℤ) := by rw [hℓ]; omega
  set σ : ℝ := (t - 1) / (3 * (R - 1)) with hσdef
  have hσpos : 0 < σ := by rw [hσdef]; exact div_pos (by linarith [ht.1]) (by positivity)
  have hσle : σ ≤ 1 / 3 := by
    rw [hσdef, div_le_iff₀ (by positivity : (0 : ℝ) < 3 * (R - 1))]
    nlinarith [ht.1, ht.2, hR]
  have hσI : σ ∈ Set.Ico 0 1 := ⟨le_of_lt hσpos, by linarith [hσle]⟩
  refine ⟨(ℓ + σ) / (D.m : ℝ), mem_Ico_div hℓ0 hℓm (le_of_lt hσpos) (by linarith [hσle]), ?_⟩
  rw [cycParam_at D R hℓ0 hℓm hσI]
  rw [show -ℓ = k by rw [hℓ]; ring]
  have hlv : (1 : ℝ) + 3 * σ * (R - 1) = t := by
    have hR1 : R - 1 ≠ 0 := by linarith
    have h1 : 3 * σ * (R - 1) = t - 1 := by
      rw [hσdef, mul_div_assoc',
        mul_div_mul_left (t - 1) (R - 1) (by norm_num : (3 : ℝ) ≠ 0), div_mul_cancel₀ _ hR1]
    rw [h1]; ring
  have hcb : cycBlock D R k σ = rayArc hN (D.A k) (D.Y k) t := by
    unfold Work.ELTop.cycBlock
    rw [if_pos hσle, hlv]
  rw [hcb, rayArc_of_ne hN (D.A k) (D.Y k) (ne_of_gt ht.1), hA]
  rw [Work.ELTop.rayPt_add_int hN (ps.get i).a t q]

/-- The piece of the second ray of the `i`-th pair below level `R` is in the image. -/
theorem mem_image_of_rayPiece_b (D : CycLift hN) {ps : List (Work.EL.CoPair hN)}
    (hM : D.Matches ps) {R : ℝ} (hR : 1 < R) (i : Fin ps.length) :
    ∀ z ∈ Work.EL.rayPiece hN (ps.get i).b 0 R, z ∈ cycParam D R '' Set.Ico 0 1 := by
  intro z hz
  obtain ⟨κ, q, hk1, hk2, hB, hY⟩ := matches_block_b hM i
  rw [rayPiece_eq_image hN hR] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  set ℓ : ℤ := -κ with hℓ
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; omega
  have hℓm : ℓ < (D.m : ℤ) := by rw [hℓ]; omega
  set σ : ℝ := 1 - (t - 1) / (3 * (R - 1)) with hσdef
  have hx : (t - 1) / (3 * (R - 1)) ≤ 1 / 3 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 3 * (R - 1))]
    have h3 : (1 / 3 : ℝ) * (3 * (R - 1)) = R - 1 := by ring
    rw [h3]
    linarith [ht.2]
  have hσ2 : 2 / 3 ≤ σ := by rw [hσdef]; linarith
  have hσ1 : σ < 1 := by
    rw [hσdef]
    have h3 : 0 < (t - 1) / (3 * (R - 1)) := div_pos (by linarith [ht.1]) (by positivity)
    linarith
  have hσI : σ ∈ Set.Ico 0 1 := ⟨by linarith, hσ1⟩
  have hσne : σ ≠ 0 := by linarith
  have h33 : 3 - 3 * σ = (t - 1) / (R - 1) := by
    have hx' : 3 * ((t - 1) / (3 * (R - 1))) = (t - 1) / (R - 1) := by
      rw [mul_div_assoc', mul_div_mul_left (t - 1) (R - 1) (by norm_num : (3 : ℝ) ≠ 0)]
    rw [hσdef, show 3 - 3 * (1 - (t - 1) / (3 * (R - 1)))
        = 3 * ((t - 1) / (3 * (R - 1))) by ring]
    exact hx'
  have hlv : 1 + (3 - 3 * σ) * (R - 1) = t := by
    rw [h33, div_mul_cancel₀ _ (by linarith : R - 1 ≠ 0)]
    ring
  refine ⟨(ℓ + σ) / (D.m : ℝ), mem_Ico_div hℓ0 hℓm (by linarith) hσ1, ?_⟩
  rw [cycParam_at D R hℓ0 hℓm hσI]
  rw [show -ℓ = κ by rw [hℓ]; ring]
  rw [Work.ELTop.cycBlock_eq_blk D hR hσI, if_neg hσne,
    blkAng_hi D hσ2, blkLev_hi hσ2 hσ1, hlv, hB]
  rw [Work.ELTop.rayPt_add_int hN (ps.get i).b t q]

/-- The equipotential point of an angle outside all the pair arcs is in the image. -/
theorem mem_image_of_eqArc (D : CycLift hN) {ps : List (Work.EL.CoPair hN)} (hM : D.Matches ps)
    {R : ℝ} (hR : 1 < R) {θ : ℝ} (hθ : θ ∈ Set.Icc 0 1)
    (hnot : ∀ P ∈ ps, ¬ Work.EL.InArc θ P.a P.b) :
    Work.EL.rayPt hN θ R ∈ cycParam D R '' Set.Ico 0 1 := by
  obtain ⟨j, hj⟩ := (matches_notInArc_iff hM θ).mp hnot
  obtain ⟨κ, hκ1, hκ2, n, hAn, hBn⟩ := exists_block_interval D j
  set θ'' : ℝ := θ + n with hθ''
  have hmem : θ'' ∈ Set.Icc (D.B (κ - 1)) (D.A κ) := by
    constructor
    · rw [hθ'', hBn]; linarith [hj.1]
    · rw [hθ'', hAn]; linarith [hj.2]
  have hAB : D.B (κ - 1) < D.A κ := by simpa using D.B_lt_A (κ - 1)
  set u : ℝ := (θ'' - D.A κ) / (D.B (κ - 1) - D.A κ) with hu
  have hden : (0 : ℝ) < D.A κ - D.B (κ - 1) := by linarith [hAB]
  have ueq : u = (D.A κ - θ'') / (D.A κ - D.B (κ - 1)) := by
    rw [hu, div_eq_div_iff (by linarith [hAB]) (by linarith [hAB])]
    ring
  have huI : u ∈ Set.Icc 0 1 := by
    constructor
    · rw [ueq]; exact div_nonneg (by linarith [hmem.2]) (le_of_lt hden)
    · rw [ueq, div_le_one hden]; linarith [hmem.1]
  have huθ : D.A κ + u * (D.B (κ - 1) - D.A κ) = θ'' := by
    have hden' : D.B (κ - 1) - D.A κ ≠ 0 := by linarith [hAB]
    rw [hu, div_mul_cancel₀ _ hden']
    ring
  set σ : ℝ := (u + 1) / 3 with hσdef
  have hσI : σ ∈ Set.Ico 0 1 := by
    rw [hσdef]; constructor <;> linarith [huI.1, huI.2]
  have hσne : σ ≠ 0 := by rw [hσdef]; linarith [huI.1]
  have hσle : σ ≤ 2 / 3 := by rw [hσdef]; linarith [huI.2]
  set ℓ : ℤ := -κ with hℓ
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; omega
  have hℓm : ℓ < (D.m : ℤ) := by rw [hℓ]; omega
  refine ⟨(ℓ + σ) / (D.m : ℝ), mem_Ico_div hℓ0 hℓm (by rw [hσdef]; linarith [huI.1]) (by linarith [hσle]), ?_⟩
  rw [cycParam_at D R hℓ0 hℓm hσI]
  rw [show -ℓ = κ by rw [hℓ]; ring]
  rw [Work.ELTop.cycBlock_eq_blk D hR hσI, if_neg hσne]
  have hba : blkAng D κ σ = θ'' := by
    rw [hσdef]
    exact (blkAng_mid D κ huI).trans huθ
  have hbl : blkLev R σ = R := by
    rw [hσdef]
    exact blkLev_mid huI
  rw [hba, hbl, hθ'']
  exact Work.ELTop.rayPt_add_int hN θ R n

/-! ## The two inclusions -/

theorem cycParam_image_subset (D : CycLift hN) (ps : List (Work.EL.CoPair hN))
    (hM : D.Matches ps) {R : ℝ} (hR : 1 < R) :
    cycParam D R '' Set.Ico 0 1 ⊆ Work.EL.polyCurve ps R := by
  rintro z ⟨s, hs, rfl⟩
  set ℓ : ℤ := ⌊(D.m : ℝ) * s⌋ with hℓ
  have hℓ0 : 0 ≤ ℓ := (floor_mem_Ico D.hm hs).1
  have hℓm : ℓ < (D.m : ℤ) := (floor_mem_Ico D.hm hs).2
  set σ : ℝ := (D.m : ℝ) * s - (ℓ : ℝ) with hσdef
  have hσ : σ ∈ Set.Ico 0 1 := by
    rw [hσdef, hℓ]
    exact fract_mem_Ico D.m s
  have hc : cycParam D R s = cycBlock D R (-ℓ) σ := by
    unfold cycParam
    rw [← hℓ, ← hσdef]
  rw [hc]
  simp only [Work.EL.polyCurve, Set.mem_setOf_eq]
  by_cases h1 : σ ≤ 1 / 3
  · have hcb : cycBlock D R (-ℓ) σ
        = rayArc hN (D.A (-ℓ)) (D.Y (-ℓ)) (1 + 3 * σ * (R - 1)) := by
      unfold Work.ELTop.cycBlock
      rw [if_pos h1]
    rw [hcb]
    have ht : (1 : ℝ) + 3 * σ * (R - 1) ∈ Set.Icc 1 R := by
      constructor
      · nlinarith [hσ.1, hR]
      · nlinarith [hσ.1, hσ.2, hR, h1]
    have himg := image_rayArc hN (D.A (-ℓ)) (matches_lands_A hM (-ℓ)) hR
    have hmem : rayArc hN (D.A (-ℓ)) (D.Y (-ℓ)) (1 + 3 * σ * (R - 1))
        ∈ Work.EL.rayPiece hN (D.A (-ℓ)) 0 R ∪ {D.Y (-ℓ)} := by
      rw [← himg]; exact ⟨_, ht, rfl⟩
    simp only [Set.mem_union, Set.mem_singleton_iff] at hmem
    obtain ⟨P, hP, q, hA, hB, hY⟩ := matches_angle hM (-ℓ)
    rcases hmem with hmem | hmem
    · left; refine ⟨P, hP, Or.inr (Or.inl ?_)⟩
      have hpe : Work.EL.rayPiece hN (D.A (-ℓ)) 0 R = Work.EL.rayPiece hN P.a 0 R := by
        rw [hA, rayPiece_add_int hN hR P.a q]
      rwa [hpe] at hmem
    · left; refine ⟨P, hP, Or.inl ?_⟩
      rw [hmem, hY]
  · by_cases h2 : σ ≤ 2 / 3
    · have hcb : cycBlock D R (-ℓ) σ
          = Work.ELTop.eqArcPt hN (D.A (-ℓ)) (D.B (-ℓ - 1)) R (3 * σ - 1) := by
        unfold Work.ELTop.cycBlock
        rw [if_neg h1, if_pos h2]
      rw [hcb]
      set u : ℝ := 3 * σ - 1 with hu
      have huI : u ∈ Set.Icc 0 1 := by
        rw [hu]; constructor <;> linarith
      set θ : ℝ := D.A (-ℓ) + u * (D.B (-ℓ - 1) - D.A (-ℓ)) with hθ
      have hunf : Work.ELTop.eqArcPt hN (D.A (-ℓ)) (D.B (-ℓ - 1)) R (3 * σ - 1)
          = Work.EL.rayPt hN θ R := by
        rw [Work.ELTop.eqArcPt, hθ, hu]
      rw [hunf]
      have hAB : D.B (-ℓ - 1) < D.A (-ℓ) := by simpa using D.B_lt_A (-ℓ - 1)
      have hθmem : θ ∈ Set.Icc (D.B (-ℓ - 1)) (D.A (-ℓ)) := by
        rw [hθ]; constructor <;> nlinarith [huI.1, huI.2, hAB]
      have hnot := notInArc_of_block_window hM (κ := -ℓ) hθmem
      obtain ⟨θ', hθ'Icc, n, hθ'n⟩ := exists_Icc_add_int θ
      have hnot' : ∀ P ∈ ps, ¬ Work.EL.InArc θ' P.a P.b := by
        intro P hP h
        exact hnot P hP ((InArc_add_int_angle θ P.a P.b n).mp (by rw [← hθ'n]; exact h))
      have hray : Work.EL.rayPt hN θ' R = Work.EL.rayPt hN θ R := by
        rw [hθ'n]; exact Work.ELTop.rayPt_add_int hN θ R n
      right
      exact ⟨θ', hθ'Icc, hnot', hray.symm⟩
    · have hcb : cycBlock D R (-ℓ) σ
          = rayArc hN (D.B (-ℓ - 1)) (D.Y (-ℓ - 1)) (1 + (3 - 3 * σ) * (R - 1)) := by
        unfold Work.ELTop.cycBlock
        rw [if_neg h1, if_neg h2]
      rw [hcb]
      have ht : (1 : ℝ) + (3 - 3 * σ) * (R - 1) ∈ Set.Icc 1 R := by
        constructor
        · nlinarith [hσ.2, hR]
        · nlinarith [hσ.1, hσ.2, hR, h2]
      have himg := image_rayArc hN (D.B (-ℓ - 1)) (matches_lands_B hM (-ℓ - 1)) hR
      have hmem : rayArc hN (D.B (-ℓ - 1)) (D.Y (-ℓ - 1)) (1 + (3 - 3 * σ) * (R - 1))
          ∈ Work.EL.rayPiece hN (D.B (-ℓ - 1)) 0 R ∪ {D.Y (-ℓ - 1)} := by
        rw [← himg]; exact ⟨_, ht, rfl⟩
      simp only [Set.mem_union, Set.mem_singleton_iff] at hmem
      obtain ⟨P, hP, q, hA, hB, hY⟩ := matches_angle hM (-ℓ - 1)
      rcases hmem with hmem | hmem
      · left; refine ⟨P, hP, Or.inr (Or.inr ?_)⟩
        have hpe : Work.EL.rayPiece hN (D.B (-ℓ - 1)) 0 R = Work.EL.rayPiece hN P.b 0 R := by
          rw [hB, rayPiece_add_int hN hR P.b q]
        rwa [hpe] at hmem
      · left; refine ⟨P, hP, Or.inl ?_⟩
        rw [hmem, hY]

theorem polyCurve_subset_cycParam_image (D : CycLift hN) (ps : List (Work.EL.CoPair hN))
    (hM : D.Matches ps) {R : ℝ} (hR : 1 < R) :
    Work.EL.polyCurve ps R ⊆ cycParam D R '' Set.Ico 0 1 := by
  intro z hz
  simp only [Work.EL.polyCurve, Set.mem_setOf_eq] at hz
  rcases hz with ⟨P, hP, hz | hz | hz⟩ | ⟨θ, hθI, hnot, hz⟩
  · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hP
    rw [hz]; exact mem_image_of_y D hM R i
  · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hP
    exact mem_image_of_rayPiece_a D hM hR i z hz
  · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hP
    exact mem_image_of_rayPiece_b D hM hR i z hz
  · rw [hz]; exact mem_image_of_eqArc D hM hR hθI hnot

theorem image_cycParam {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ} (D : Work.ELTop.CycLift hN)
    (ps : List (Work.EL.CoPair hN)) (hM : D.Matches ps) {R : ℝ} (hR : 1 < R) :
    Work.ELTop.cycParam D R '' Set.Ico 0 1 = Work.EL.polyCurve ps R :=
  Set.Subset.antisymm (cycParam_image_subset D ps hM hR) (polyCurve_subset_cycParam_image D ps hM hR)

end Work.ELTop.PolyCurve
