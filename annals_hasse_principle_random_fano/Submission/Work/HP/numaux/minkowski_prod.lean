import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.numaux.Defs
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.lam_basic
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.Lat.detL_basis_gram
import Submission.Work.HP.numaux.ker_projScale_inf

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Finset

namespace Work.HP.numaux

open Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If `L` contains `i` linearly independent vectors of norm at most `ρ`, then `lam L i ≤ ρ`. -/
lemma lam_le_of {L : Submodule ℤ (ι → ℤ)} {i : ℕ} {f : Fin i → ι → ℤ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hfL : ∀ j, f j ∈ L) (hLI : LinearIndependent ℤ f) (hn : ∀ j, eNorm (f j) ≤ ρ) :
    lam L i ≤ ρ := by
  rw [lam_eq_sInf]
  exact csInf_le (bddBelow_lamSet L i) ⟨hρ, f, hfL, hLI, hn⟩

/-- `lam · i` is monotone with respect to inclusion of lattices. -/
lemma lam_le_of_le {L M : Submodule ℤ (ι → ℤ)} (h : M ≤ L) {i : ℕ} (hi : i ≤ rk M) :
    lam L i ≤ lam M i := by
  rw [lam_eq_sInf, lam_eq_sInf]
  refine le_csInf (lamSet_nonempty M hi) ?_
  rintro ρ ⟨hρ0, f, hfL, hLI, hfρ⟩
  exact csInf_le (bddBelow_lamSet L i) ⟨hρ0, f, fun j => h (hfL j), hLI, hfρ⟩

/-- A shortest nonzero vector of a nonzero lattice exists. -/
lemma exists_shortest_aux (L : Submodule ℤ (ι → ℤ)) (hL : L ≠ ⊥) :
    ∃ b : ι → ℤ, b ∈ L ∧ b ≠ 0 ∧ eNorm b = lam L 1 ∧
      ∀ x ∈ L, x ≠ 0 → eNorm b ≤ eNorm x := by
  have hrk : 1 ≤ rk L := by
    rw [rk]
    by_contra h
    push_neg at h
    have h0 : Module.finrank ℤ L = 0 := Nat.lt_one_iff.mp h
    exact hL (Submodule.finrank_eq_zero.mp h0)
  obtain ⟨f, hfL, hfLI, hfn⟩ :=
    lam_witness L hrk (ρ := lam L 1 + 1) (by linarith [lam_nonneg L 1])
  have hf0 : f 0 ≠ 0 := hfLI.ne_zero 0
  set S : Set (ι → ℤ) := {x | x ∈ L ∧ x ≠ 0 ∧ eNorm x ≤ lam L 1 + 1} with hS
  have hSfin : S.Finite :=
    (MDBasic.finite_eNorm_le (ι := ι) (lam L 1 + 1)).subset (fun x hx => hx.2.2)
  have hSne : S.Nonempty := ⟨f 0, hfL 0, hf0, hfn 0⟩
  obtain ⟨b, hbS, hbmin⟩ := Set.exists_min_image S eNorm hSfin hSne
  obtain ⟨hbL, hb0, hbn⟩ := hbS
  have hbmin' : ∀ x ∈ L, x ≠ 0 → eNorm b ≤ eNorm x := by
    intro x hxL hx0
    by_cases hx : eNorm x ≤ lam L 1 + 1
    · exact hbmin x ⟨hxL, hx0, hx⟩
    · push_neg at hx
      calc eNorm b ≤ lam L 1 + 1 := hbn
        _ ≤ eNorm x := le_of_lt hx
  refine ⟨b, hbL, hb0, ?_, hbmin'⟩
  refine le_antisymm ?_ (lam_one_le_eNorm L hbL hb0)
  refine le_csInf (lamSet_nonempty L hrk) ?_
  rintro ρ ⟨-, g, hgL, hgLI, hgρ⟩
  have hg0 : g 0 ≠ 0 := hgLI.ne_zero 0
  by_cases hgc : eNorm (g 0) ≤ lam L 1 + 1
  · exact (hbmin (g 0) ⟨hgL 0, hg0, hgc⟩).trans (hgρ 0)
  · push_neg at hgc
    calc eNorm b ≤ lam L 1 + 1 := hbn
      _ ≤ eNorm (g 0) := le_of_lt hgc
      _ ≤ ρ := hgρ 0

/-- The integer dot product of a nonzero vector with itself is strictly positive. -/
lemma dotZ_self_pos_aux {b : ι → ℤ} (hb : b ≠ 0) : 0 < dotZ b b := by
  rw [dotZ_apply]
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hb
  have hle : b i0 * b i0 ≤ ∑ i, b i * b i := by
    simpa using Finset.single_le_sum (s := Finset.univ)
      (f := fun i => b i * b i) (fun i _ => mul_self_nonneg (b i)) (Finset.mem_univ i0)
  have hpos : 0 < b i0 * b i0 := mul_self_pos.mpr hi0
  linarith

/-- `eNorm` scales by the absolute value of a real scalar. -/
lemma eNorm_real_smul_aux {w b : ι → ℤ} {c : ℝ} (h : ∀ i, ((w i : ℝ)) = c * ((b i : ℝ))) :
    eNorm w = |c| * eNorm b := by
  have hw : eNorm w ^ 2 = ∑ i, ((w i : ℝ)) ^ 2 := by
    rw [eNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  have hb2 : eNorm b ^ 2 = ∑ i, ((b i : ℝ)) ^ 2 := by
    rw [eNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  have hsum : ∑ i, ((w i : ℝ)) ^ 2 = c ^ 2 * ∑ i, ((b i : ℝ)) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [h i]; ring
  have hsquares : eNorm w ^ 2 = c ^ 2 * eNorm b ^ 2 := by rw [hw, hb2, hsum]
  have h2 : Real.sqrt (c ^ 2 * eNorm b ^ 2) = |c| * eNorm b := by
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, Real.sqrt_sq (eNorm_nonneg b)]
  have hsq : eNorm w = Real.sqrt (eNorm w ^ 2) := (Real.sqrt_sq (eNorm_nonneg w)).symm
  rw [hsq, hsquares, h2]

theorem ker_projScale_inf_aux (L : Submodule ℤ (ι → ℤ))
    {b : ι → ℤ} (hb : b ∈ L) (hb0 : b ≠ 0)
    (hmin : ∀ x ∈ L, x ≠ 0 → Work.HP.eNorm b ≤ Work.HP.eNorm x) :
    LinearMap.ker (Work.HP.projScale b) ⊓ L = Submodule.span ℤ {b} := by
  refine le_antisymm ?_ ?_
  · -- `ker (projScale b) ⊓ L ≤ ℤb`
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hxker, hxL⟩ := hx
    have hker := LinearMap.mem_ker.mp hxker
    rw [projScale_apply] at hker
    set N : ℤ := dotZ b b with hN
    set d : ℤ := dotZ x b with hd
    have hminN : 0 < N := by rw [hN]; exact dotZ_self_pos_aux hb0
    have hEq : N • x = d • b := by
      rw [hN, hd]
      exact sub_eq_zero.mp hker
    have hcoord : ∀ i, N * x i = d * b i := by
      intro i
      have := congrFun hEq i
      simpa [Pi.smul_apply, smul_eq_mul] using this
    set m : ℤ := d / N with hm
    set r : ℤ := d % N with hr
    have hmr : m * N + r = d := by rw [hm, hr]; exact Int.ediv_mul_add_emod d N
    have hr_nonneg : 0 ≤ r := by rw [hr]; exact Int.emod_nonneg d (ne_of_gt hminN)
    have hr_lt : r < N := by rw [hr]; exact Int.emod_lt_of_pos d hminN
    have hw_mem : x - m • b ∈ L := Submodule.sub_mem _ hxL (Submodule.smul_mem _ m hb)
    have hwi : ∀ i, N * ((x - m • b) i) = r * (b i) := by
      intro i
      have h2 : (x - m • b) i = x i - m * b i := by
        rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have h1 : N * (x i - m * b i) = N * x i - (N * m) * b i := by ring
      rw [h2, h1, hcoord i]
      have h3 : d * b i - (N * m) * b i = (d - N * m) * b i := by ring
      rw [h3]
      have h4 : d - N * m = r := by linarith [hmr]
      rw [h4]
    have hNposR : 0 < (N : ℝ) := by exact_mod_cast hminN
    have hnn : 0 ≤ (r : ℝ) / (N : ℝ) :=
      div_nonneg (by exact_mod_cast hr_nonneg) (by exact_mod_cast (le_of_lt hminN))
    have hwR : ∀ i, (((x - m • b) i : ℝ)) = ((r : ℝ) / (N : ℝ)) * ((b i : ℝ)) := by
      intro i
      have hwiR : (N : ℝ) * (((x - m • b) i) : ℝ) = (r : ℝ) * ((b i : ℝ)) := by
        exact_mod_cast hwi i
      rw [div_mul_eq_mul_div, eq_div_iff (ne_of_gt hNposR), mul_comm]
      exact hwiR
    have hwe : eNorm (x - m • b) = (r : ℝ) / (N : ℝ) * eNorm b := by
      rw [eNorm_real_smul_aux hwR, abs_of_nonneg hnn]
    by_cases hr0 : r = 0
    · -- then `x = m • b`
      have hxeq : x = m • b := by
        have hzero : x - m • b = 0 := by
          funext i
          have h0 : N * ((x - m • b) i) = 0 := by rw [hwi i, hr0]; ring
          have hi0 : ((x - m • b) i) = 0 := by
            rcases mul_eq_zero.mp h0 with h | h
            · exact absurd h (ne_of_gt hminN)
            · exact h
          exact hi0
        exact sub_eq_zero.mp hzero
      exact Submodule.mem_span_singleton.mpr ⟨m, hxeq.symm⟩
    · -- otherwise `x - m • b ∈ L` is nonzero of strictly smaller norm: contradiction
      exfalso
      have hrpos : 0 < r := lt_of_le_of_ne hr_nonneg (Ne.symm hr0)
      have hNr : (r : ℝ) < (N : ℝ) := by exact_mod_cast hr_lt
      have hrdivlt : (r : ℝ) / (N : ℝ) < 1 := by rw [div_lt_one hNposR]; exact hNr
      have heb : 0 < eNorm b := eNorm_pos_iff.mpr hb0
      have hlt : eNorm (x - m • b) < eNorm b := by
        rw [hwe]
        calc (r : ℝ) / (N : ℝ) * eNorm b < 1 * eNorm b :=
              mul_lt_mul_of_pos_right hrdivlt heb
          _ = eNorm b := one_mul _
      have hwpos : 0 < eNorm (x - m • b) := by
        rw [hwe]
        exact mul_pos (div_pos (by exact_mod_cast hrpos) hNposR) heb
      have hwne : x - m • b ≠ 0 := by
        intro hh
        have := hwpos
        rw [hh] at this
        simp [eNorm] at this
      exact absurd (hmin (x - m • b) hw_mem hwne) (not_le.mpr hlt)
  · -- `ℤb ≤ ker (projScale b) ⊓ L`
    rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_inf]
    exact ⟨LinearMap.mem_ker.mpr (by rw [projScale_apply, sub_self]), hb⟩

/-- The scaled projection `projScale b` drops the rank by one when `b` is a shortest vector. -/
lemma rk_map_projScale_aux (L : Submodule ℤ (ι → ℤ)) {b : ι → ℤ} (hb : b ∈ L) (hb0 : b ≠ 0)
    (hmin : ∀ x ∈ L, x ≠ 0 → eNorm b ≤ eNorm x) :
    rk (Submodule.map (projScale b) L) = rk L - 1 := by
  have hker : LinearMap.ker (projScale b) ⊓ L = Submodule.span ℤ {b} :=
    ker_projScale_inf_aux L hb hb0 hmin
  let f : L →ₗ[ℤ] (ι → ℤ) := (projScale b).comp L.subtype
  have hrange : f.range = Submodule.map (projScale b) L := by
    ext x
    rw [LinearMap.mem_range, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨(y : ι → ℤ), y.2, hy⟩
    · rintro ⟨y, hyL, hyx⟩
      exact ⟨⟨y, hyL⟩, hyx⟩
  have hkerf : f.ker = Submodule.span ℤ {⟨b, hb⟩} := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
    constructor
    · intro hx
      have hx1 : (x : ι → ℤ) ∈ LinearMap.ker (projScale b) ⊓ L := ⟨hx, x.2⟩
      rw [hker, Submodule.mem_span_singleton] at hx1
      obtain ⟨m, hm⟩ := hx1
      exact ⟨m, Subtype.ext (by simpa using hm)⟩
    · rintro ⟨m, hm⟩
      have hval : (x : ι → ℤ) = m • b := by
        have := congrArg (fun t : L => (t : ι → ℤ)) hm
        simpa using this.symm
      show (projScale b) ↑x = 0
      rw [hval, map_smul, show (projScale b) b = 0 from by rw [projScale_apply, sub_self],
        smul_zero]
  have hfin1 : Module.finrank ℤ ↥f.ker = 1 := by
    have hmem : (⟨b, hb⟩ : L) ∈ f.ker := by
      rw [hkerf]
      exact Submodule.mem_span_singleton_self _
    set u : ↥f.ker := ⟨⟨b, hb⟩, hmem⟩ with hu
    have hu0 : u ≠ 0 := by
      intro hh
      refine hb0 ?_
      have := congrArg (fun t : ↥f.ker => ((t : L) : ι → ℤ)) hh
      simpa [hu, Subtype.ext_iff] using this
    have hli : LinearIndependent ℤ (fun _ : Fin 1 => u) := by
      rw [linearIndependent_unique_iff]
      exact hu0
    have hsp : ⊤ ≤ Submodule.span ℤ (Set.range (fun _ : Fin 1 => u)) := by
      intro x _
      have hx : (x : L) ∈ Submodule.span ℤ {⟨b, hb⟩} := by
        rw [← hkerf]; exact x.2
      rw [Submodule.mem_span_singleton] at hx
      obtain ⟨a, ha⟩ := hx
      have hxu : x = a • u := by
        refine Subtype.ext ?_
        have hcoe : ((a • u : ↥f.ker) : L) = a • (⟨b, hb⟩ : L) := by rw [hu]; simp
        rw [hcoe]
        exact ha.symm
      rw [hxu]
      exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_range_self (default : Fin 1)))
    rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)]
    simp
  have hq := Submodule.finrank_quotient_add_finrank (R := ℤ) f.ker
  rw [LinearEquiv.finrank_eq f.quotKerEquivRange, hfin1, hrange] at hq
  have : Module.finrank ℤ ↥(Submodule.map (projScale b) L) = Module.finrank ℤ ↥L - 1 := by
    omega
  exact this

/-- Base case: for lattices of rank at most one the product of successive minima is at most
the covolume. -/
lemma minkowski_base_aux (L : Submodule ℤ (ι → ℤ)) (h : rk L ≤ 1) :
    (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ detL L := by
  obtain ⟨n, c⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) L
  have hn : n = rk L := by
    show n = Module.finrank ℤ ↥L
    rw [Module.finrank_eq_card_basis c]
    simp
  rw [← hn] at h ⊢
  have hgram := Work.HP.Lat.detL_basis_gram L c
  interval_cases n
  · rw [hgram, Matrix.det_isEmpty, Real.sqrt_one]
    simp
  · rw [hgram]
    have hdet : (Matrix.of fun i j : Fin 1 =>
        ∑ x, (((c i : ι → ℤ) x : ℝ) * ((c j : ι → ℤ) x : ℝ))).det
        = eNorm ((c 0 : L) : ι → ℤ) ^ 2 := by
      rw [Matrix.det_fin_one, Matrix.of_apply]
      rw [eNorm_sq_eq, dotZ_apply]
      push_cast
      ring
    rw [hdet, Real.sqrt_sq (eNorm_nonneg _)]
    have hv0 : ((c 0 : L) : ι → ℤ) ≠ 0 := by
      intro hh
      exact c.linearIndependent.ne_zero 0 (Subtype.ext hh)
    simpa using lam_one_le_eNorm L (c 0).2 hv0

/-! ## The scaled projection: lifting bound

Elementary identities for the integer pairing `dotZ` used below. -/

private lemma dotZ_smul_right (m : ℤ) (x y : ι → ℤ) : dotZ x (m • y) = m * dotZ x y := by
  simp only [dotZ, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

private lemma dotZ_add_right (x y z : ι → ℤ) : dotZ x (y + z) = dotZ x y + dotZ x z := by
  simp only [dotZ, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma dotZ_sub (x y w : ι → ℤ) : dotZ (x - y) w = dotZ x w - dotZ y w := by
  simp only [dotZ, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private lemma dotZ_sub_right (x y z : ι → ℤ) : dotZ x (y - z) = dotZ x y - dotZ x z := by
  simp only [dotZ, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private lemma dotZ_smul_smul (m n : ℤ) (x y : ι → ℤ) :
    dotZ (m • x) (n • y) = m * n * dotZ x y := by
  rw [dotZ_smul, dotZ_smul_right]
  ring

private lemma dotZ_self_add (u v : ι → ℤ) :
    dotZ (u + v) (u + v) = dotZ u u + 2 * dotZ u v + dotZ v v := by
  rw [dotZ_add, dotZ_add_right, dotZ_add_right, dotZ_comm v u]
  ring

/-- **Lifting bound.**  For `y` in the image of the scaled projection `projScale b` there is a
lift `x ∈ L` with `projScale b x = y` whose norm is controlled by the norm of `y`. -/
lemma projScale_lift_bound (L : Submodule ℤ (ι → ℤ)) {b : ι → ℤ} (hb : b ∈ L) (hb0 : b ≠ 0)
    {y : ι → ℤ} (hy : y ∈ Submodule.map (projScale b) L) :
    ∃ x ∈ L, projScale b x = y ∧
      eNorm x ^ 2 ≤ eNorm y ^ 2 / (eNorm b) ^ 4 + (eNorm b) ^ 2 / 4 := by
  obtain ⟨x₀, hx₀L, hx₀⟩ := hy
  have hbT : (projScale b) b = 0 := by rw [projScale_apply, sub_self]
  set N : ℤ := dotZ b b with hN
  set d : ℤ := dotZ x₀ b with hd
  have hNpos : 0 < N := by rw [hN]; exact dotZ_self_pos_aux hb0
  set k : ℤ := ⌊(d : ℚ) / (N : ℚ) + 1 / 2⌋ with hk
  have hkabs : |(d : ℚ) / (N : ℚ) - (k : ℚ)| ≤ 1 / 2 := by
    have h1 : (k : ℚ) ≤ (d : ℚ) / (N : ℚ) + 1 / 2 := by
      rw [hk]; exact Int.floor_le _
    have h2 : (d : ℚ) / (N : ℚ) + 1 / 2 < (k : ℚ) + 1 := by
      rw [hk]; exact Int.lt_floor_add_one _
    rw [abs_le]
    constructor <;> linarith
  set e : ℤ := k * N - d with he
  have heabs : |((e : ℤ) : ℚ)| ≤ (N : ℚ) / 2 := by
    have hNq : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hNpos
    have hα : ((N : ℚ)) * ((d : ℚ) / (N : ℚ)) = (d : ℚ) := by
      field_simp
    have hkey : ((N : ℚ)) * ((k : ℚ) - (d : ℚ) / (N : ℚ)) = ((e : ℤ) : ℚ) := by
      rw [he]
      push_cast
      rw [mul_sub, hα]
      ring
    rw [← hkey, abs_mul, abs_of_pos hNq, abs_sub_comm]
    calc (N : ℚ) * |(d : ℚ) / (N : ℚ) - (k : ℚ)| ≤ (N : ℚ) * (1 / 2) :=
          mul_le_mul_of_nonneg_left hkabs (le_of_lt hNq)
      _ = (N : ℚ) / 2 := by ring
  refine ⟨x₀ - k • b, Submodule.sub_mem _ hx₀L (Submodule.smul_mem _ k hb), ?_, ?_⟩
  · rw [map_sub, map_smul, hbT, smul_zero, sub_zero, hx₀]
  · set x : ι → ℤ := x₀ - k • b with hx
    have hycoord : y = N • x + e • b := by
      funext i
      have h2 : y i = N * x₀ i - d * b i := by
        have h := congrFun hx₀ i
        rw [projScale_apply] at h
        simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hN, hd] using h.symm
      have h3 : x i = x₀ i - k * b i := by
        simp [hx, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have h4 : (N • x + e • b) i = N * x i + e * b i := by
        simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [h4, h2, h3, he]
      ring
    have hxb : dotZ x b = -e := by
      rw [hx, dotZ_sub, dotZ_smul, ← hd, ← hN, he]
      ring
    have hyy : dotZ y y = N ^ 2 * dotZ x x - N * e ^ 2 := by
      rw [hycoord, dotZ_self_add, dotZ_smul_smul, dotZ_smul_smul, dotZ_smul_smul, hxb, ← hN]
      ring
    have hE : eNorm y ^ 2 = ((N : ℝ)) ^ 2 * eNorm x ^ 2 - (N : ℝ) * ((e : ℝ)) ^ 2 := by
      rw [eNorm_sq_eq, eNorm_sq_eq, hyy]
      push_cast
      ring
    have hNb : (eNorm b) ^ 2 = (N : ℝ) := by
      rw [eNorm_sq_eq, ← hN]
    have heN : ((e : ℝ)) ^ 2 ≤ ((N : ℝ)) ^ 2 / 4 := by
      have h1 : |((e : ℤ) : ℝ)| ≤ ((N : ℤ) : ℝ) / 2 := by
        have h2 : |((e : ℤ) : ℚ)| ≤ ((N : ℤ) : ℚ) / 2 := heabs
        exact_mod_cast h2
      have h3 : |((e : ℤ) : ℝ)| ^ 2 ≤ (((N : ℤ) : ℝ) / 2) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [sq_abs] at h3
      nlinarith [h3]
    have hNposR : 0 < (N : ℝ) := by exact_mod_cast hNpos
    have h4 : (eNorm b) ^ 4 = ((N : ℝ)) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hNb]
    have hmain : eNorm x ^ 2 = eNorm y ^ 2 / (eNorm b) ^ 4 + ((e : ℝ)) ^ 2 / (eNorm b) ^ 2 := by
      rw [hE, h4, hNb]
      field_simp
      ring
    rw [hmain]
    have hle : ((e : ℝ)) ^ 2 / (eNorm b) ^ 2 ≤ (eNorm b) ^ 2 / 4 := by
      rw [hNb]
      rw [div_le_div_iff₀ hNposR (by norm_num : (0 : ℝ) < 4)]
      nlinarith [heN]
    linarith

/-- **The `2/√3` chain.**  Given `i - 1` linearly independent vectors of the image of the scaled
projection of norm at most `ρ`, the lattice `L` contains `i` linearly independent vectors of norm
at most `(2/√3) ρ / ‖b‖²`. -/
lemma projscale_lift_chain_aux (L : Submodule ℤ (ι → ℤ)) {b : ι → ℤ} (hb : b ∈ L) (hb0 : b ≠ 0)
    (hmin : ∀ x ∈ L, x ≠ 0 → eNorm b ≤ eNorm x)
    {i : ℕ} (h2 : 2 ≤ i) {ρ : ℝ} {f : Fin (i - 1) → ι → ℤ}
    (hfL : ∀ j, f j ∈ Submodule.map (projScale b) L)
    (hfLI : LinearIndependent ℤ f) (hfn : ∀ j, eNorm (f j) ≤ ρ) :
    ∃ g : Fin ((i - 1) + 1) → ι → ℤ, (∀ j, g j ∈ L) ∧ LinearIndependent ℤ g ∧
      ∀ j, eNorm (g j) ≤ 2 / Real.sqrt 3 * ρ / (eNorm b) ^ 2 := by
  have hbT : (projScale b) b = 0 := by rw [projScale_apply, sub_self]
  have hs : 0 < eNorm b := eNorm_pos_of_ne_zero hb0
  have hs2pos : 0 < (eNorm b) ^ 2 := by positivity
  have hlow : ∀ y ∈ Submodule.map (projScale b) L, y ≠ 0 →
      Real.sqrt 3 / 2 * (eNorm b) ^ 3 ≤ eNorm y := by
    intro y hy hy0
    obtain ⟨x, hxL, hxT, hxb⟩ := projScale_lift_bound L hb hb0 hy
    have hx0 : x ≠ 0 := by
      intro hh
      rw [hh] at hxT
      simp only [map_zero] at hxT
      exact hy0 hxT.symm
    have hxmin : eNorm b ≤ eNorm x := hmin x hxL hx0
    have hs4 : 0 < (eNorm b) ^ 4 := by positivity
    have hxb' : eNorm x ^ 2 * (eNorm b) ^ 4 ≤ eNorm y ^ 2 + (eNorm b) ^ 6 / 4 := by
      calc eNorm x ^ 2 * (eNorm b) ^ 4
          ≤ (eNorm y ^ 2 / (eNorm b) ^ 4 + (eNorm b) ^ 2 / 4) * (eNorm b) ^ 4 :=
            mul_le_mul_of_nonneg_right hxb (le_of_lt hs4)
        _ = eNorm y ^ 2 + (eNorm b) ^ 6 / 4 := by
            rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hs4)]
            ring
    have h1 : (Real.sqrt 3 / 2 * (eNorm b) ^ 3) ^ 2 ≤ (eNorm y) ^ 2 := by
      have hrew : (Real.sqrt 3 / 2 * (eNorm b) ^ 3) ^ 2 = 3 / 4 * (eNorm b) ^ 6 := by
        rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
        ring
      rw [hrew]
      have hx2 : (eNorm b) ^ 2 ≤ eNorm x ^ 2 := by
        nlinarith [hxmin, eNorm_nonneg b, eNorm_nonneg x]
      have hs6 : (eNorm b) ^ 6 ≤ eNorm x ^ 2 * (eNorm b) ^ 4 := by
        calc (eNorm b) ^ 6 = (eNorm b) ^ 2 * (eNorm b) ^ 4 := by ring
          _ ≤ eNorm x ^ 2 * (eNorm b) ^ 4 := mul_le_mul_of_nonneg_right hx2 (by positivity)
      nlinarith [hxb', hs6]
    calc Real.sqrt 3 / 2 * (eNorm b) ^ 3
        = Real.sqrt ((Real.sqrt 3 / 2 * (eNorm b) ^ 3) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt ((eNorm y) ^ 2) := Real.sqrt_le_sqrt h1
      _ = eNorm y := Real.sqrt_sq (eNorm_nonneg y)
  haveI : NeZero (i - 1) := ⟨by omega⟩
  have hf0 : f 0 ≠ 0 := hfLI.ne_zero 0
  have hsp3 : 0 < Real.sqrt 3 := Real.sqrt_pos_of_pos (by norm_num)
  have hs3 : (eNorm b) ^ 3 ≤ 2 / Real.sqrt 3 * ρ := by
    have h0 : Real.sqrt 3 / 2 * (eNorm b) ^ 3 ≤ ρ := (hlow (f 0) (hfL 0) hf0).trans (hfn 0)
    have h0' : Real.sqrt 3 * (eNorm b) ^ 3 ≤ 2 * ρ := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hsp3]
    calc (eNorm b) ^ 3 * Real.sqrt 3 = Real.sqrt 3 * (eNorm b) ^ 3 := by ring
      _ ≤ 2 * ρ := h0'
  have hρpos : 0 < ρ :=
    pos_of_mul_pos_right (show 0 < 2 / Real.sqrt 3 * ρ from lt_of_lt_of_le (by positivity) hs3)
      (le_of_lt (div_pos (by norm_num) hsp3))
  have hc : (2 / Real.sqrt 3) ^ 2 = 4 / 3 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hsq : 3 * (eNorm b) ^ 6 ≤ 4 * ρ ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (eNorm b) ^ 3) hs3 2
    have h' : (eNorm b) ^ 6 ≤ (4 / 3) * ρ ^ 2 := by
      calc (eNorm b) ^ 6 = ((eNorm b) ^ 3) ^ 2 := by ring
        _ ≤ (2 / Real.sqrt 3 * ρ) ^ 2 := h
        _ = 4 / 3 * ρ ^ 2 := by rw [mul_pow, hc]
    linarith
  have hlift : ∀ j : Fin (i - 1), ∃ x ∈ L, projScale b x = f j ∧
      eNorm x ^ 2 ≤ eNorm (f j) ^ 2 / (eNorm b) ^ 4 + (eNorm b) ^ 2 / 4 :=
    fun j => projScale_lift_bound L hb hb0 (hfL j)
  let xl : Fin (i - 1) → ι → ℤ := fun j => Classical.choose (hlift j)
  have hxlL : ∀ j, xl j ∈ L := fun j => (Classical.choose_spec (hlift j)).1
  have hxlT : ∀ j, projScale b (xl j) = f j := fun j => (Classical.choose_spec (hlift j)).2.1
  have hxln : ∀ j, eNorm (xl j) ^ 2 ≤ eNorm (f j) ^ 2 / (eNorm b) ^ 4 + (eNorm b) ^ 2 / 4 :=
    fun j => (Classical.choose_spec (hlift j)).2.2
  have hbound : ∀ j : Fin (i - 1),
      eNorm (xl j) ≤ 2 / Real.sqrt 3 * ρ / (eNorm b) ^ 2 := by
    intro j
    have hmain : eNorm (xl j) ^ 2 ≤ (2 / Real.sqrt 3 * ρ / (eNorm b) ^ 2) ^ 2 := by
      have h1 : eNorm (f j) ^ 2 / (eNorm b) ^ 4 ≤ ρ ^ 2 / (eNorm b) ^ 4 :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (eNorm_nonneg _) (hfn j) 2) (by positivity)
      have h2 : (eNorm b) ^ 2 / 4 ≤ ρ ^ 2 / (3 * (eNorm b) ^ 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) (by positivity)]
        nlinarith [hsq]
      have hrew : (2 / Real.sqrt 3 * ρ / (eNorm b) ^ 2) ^ 2 = (4 / 3) * ρ ^ 2 / (eNorm b) ^ 4 := by
        rw [div_pow, mul_pow, hc]
        ring
      rw [hrew]
      calc eNorm (xl j) ^ 2
          ≤ eNorm (f j) ^ 2 / (eNorm b) ^ 4 + (eNorm b) ^ 2 / 4 := hxln j
        _ ≤ ρ ^ 2 / (eNorm b) ^ 4 + ρ ^ 2 / (3 * (eNorm b) ^ 4) := add_le_add h1 h2
        _ = 4 / 3 * ρ ^ 2 / (eNorm b) ^ 4 := by
            field_simp
            ring
    calc eNorm (xl j) = Real.sqrt ((eNorm (xl j)) ^ 2) := (Real.sqrt_sq (eNorm_nonneg _)).symm
      _ ≤ Real.sqrt ((2 / Real.sqrt 3 * ρ / (eNorm b) ^ 2) ^ 2) := Real.sqrt_le_sqrt hmain
      _ = 2 / Real.sqrt 3 * ρ / (eNorm b) ^ 2 := Real.sqrt_sq (by positivity)
  have hbnd : eNorm b ≤ 2 / Real.sqrt 3 * ρ / (eNorm b) ^ 2 := by
    rw [le_div_iff₀ hs2pos]
    calc eNorm b * (eNorm b) ^ 2 = (eNorm b) ^ 3 := by ring
      _ ≤ 2 / Real.sqrt 3 * ρ := hs3
  let φ : (ι → ℤ) →ₗ[ℤ] ℤ :=
    { toFun := fun y => dotZ y b
      map_add' := fun x y => dotZ_add x y b
      map_smul' := fun m x => dotZ_smul m x b }
  have hφf : ∀ j, φ (f j) = 0 := by
    intro j
    rw [← hxlT j]
    show dotZ (projScale b (xl j)) b = 0
    rw [projScale_apply, dotZ_sub, dotZ_smul, dotZ_smul]
    ring
  have hφb : φ b = dotZ b b := rfl
  have hbnot : b ∉ Submodule.span ℤ (Set.range f) := by
    have hle : Submodule.span ℤ (Set.range f) ≤ LinearMap.ker φ :=
      Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact LinearMap.mem_ker.mpr (hφf j))
    intro hbspan
    have h0 : φ b = 0 := LinearMap.mem_ker.mp (hle hbspan)
    rw [hφb] at h0
    exact (ne_of_gt (dotZ_self_pos_aux hb0)) h0
  let g : Fin ((i - 1) + 1) → ι → ℤ := Fin.cons b xl
  have hg0 : g 0 = b := rfl
  have hgs : ∀ j : Fin (i - 1), g j.succ = xl j := fun j => rfl
  refine ⟨g, ?_, ?_, ?_⟩
  · intro j
    refine Fin.cases ?_ ?_ j
    · simpa [hg0] using hb
    · intro j
      simpa [hgs j] using hxlL j
  · rw [Fintype.linearIndependent_iff]
    intro a ha
    have hmap : ∑ j : Fin (i - 1), a j.succ • f j = 0 := by
      have h1 : projScale b (∑ k : Fin ((i - 1) + 1), a k • g k) = 0 := by
        rw [ha, map_zero]
      rw [map_sum, Fin.sum_univ_succ] at h1
      have h2 : (projScale b) (a 0 • g 0) = 0 := by
        rw [hg0, map_smul, hbT, smul_zero]
      have h3 : (∑ j : Fin (i - 1), (projScale b) (a j.succ • g j.succ))
          = ∑ j : Fin (i - 1), a j.succ • f j :=
        Finset.sum_congr rfl (fun j _ => by rw [hgs j, map_smul, hxlT j])
      rw [h2, zero_add, h3] at h1
      exact h1
    have h2 : ∀ j : Fin (i - 1), a j.succ = 0 :=
      fun j => (Fintype.linearIndependent_iff.mp hfLI) (fun k => a k.succ) hmap j
    have h3 : a 0 • b = 0 := by
      have h5 := ha
      rw [Fin.sum_univ_succ] at h5
      have h6 : (∑ j : Fin (i - 1), a j.succ • g j.succ) = 0 :=
        Finset.sum_eq_zero (fun j _ => by rw [hgs j, h2 j, zero_smul])
      rw [h6, add_zero] at h5
      rwa [hg0] at h5
    have h0eq : a 0 = 0 := by
      rcases smul_eq_zero.mp h3 with h | h
      · exact h
      · exact absurd h hb0
    intro k
    exact Fin.cases h0eq (fun j => h2 j) k
  · intro j
    refine Fin.cases ?_ ?_ j
    · simpa [hg0] using hbnd
    · intro j
      simpa [hgs j] using hbound j


/-- The `i`-th minimum of `L` is at most `(2/√3)` times the `(i-1)`-st minimum of the image of
the scaled projection `projScale b`, divided by `‖b‖²`. -/
lemma lam_projScale_le_aux (L : Submodule ℤ (ι → ℤ)) {b : ι → ℤ} (hb : b ∈ L) (hb0 : b ≠ 0)
    (hmin : ∀ x ∈ L, x ≠ 0 → eNorm b ≤ eNorm x) {i : ℕ} (h2 : 2 ≤ i) (hi : i ≤ rk L) :
    lam L i ≤ 2 / Real.sqrt 3 * lam (Submodule.map (projScale b) L) (i - 1) / (eNorm b) ^ 2 := by
  have hrk : rk (Submodule.map (projScale b) L) = rk L - 1 :=
    rk_map_projScale_aux L hb hb0 hmin
  have hle : i - 1 ≤ rk (Submodule.map (projScale b) L) := by omega
  have hi' : i = (i - 1) + 1 := by omega
  have hs : 0 < eNorm b := eNorm_pos_of_ne_zero hb0
  refine le_of_forall_pos_le_add ?_
  intro δ hδ
  set ε : ℝ := δ * Real.sqrt 3 * (eNorm b) ^ 2 / 2 with hε
  have hεpos : 0 < ε := by
    rw [hε]
    exact div_pos (mul_pos (mul_pos hδ (Real.sqrt_pos_of_pos (by norm_num))) (by positivity))
      (by norm_num)
  obtain ⟨f, hfL, hfLI, hfn⟩ :=
    lam_witness (Submodule.map (projScale b) L) hle
      (ρ := lam (Submodule.map (projScale b) L) (i - 1) + ε) (by linarith)
  obtain ⟨g, hgL, hgLI, hgn⟩ := projscale_lift_chain_aux L hb hb0 hmin h2 hfL hfLI hfn
  have hcastinj : Function.Injective (Fin.cast hi') := by
    intro a c hac
    exact Fin.ext (by simpa using congrArg Fin.val hac)
  have hLI : LinearIndependent ℤ (fun j : Fin i => g (Fin.cast hi' j)) :=
    hgLI.comp (Fin.cast hi') hcastinj
  have hbnd : ∀ j : Fin i, eNorm (g (Fin.cast hi' j))
      ≤ 2 / Real.sqrt 3 * (lam (Submodule.map (projScale b) L) (i - 1) + ε) / (eNorm b) ^ 2 :=
    fun j => hgn _
  have hmain : lam L i
      ≤ 2 / Real.sqrt 3 * (lam (Submodule.map (projScale b) L) (i - 1) + ε) / (eNorm b) ^ 2 := by
    refine lam_le_of ?_ (fun j => hgL _) hLI hbnd
    exact div_nonneg (mul_nonneg (by positivity)
      (add_nonneg (lam_nonneg _ _) (le_of_lt hεpos))) (by positivity)
  have hεdiv : 2 / Real.sqrt 3 * ε / (eNorm b) ^ 2 = δ := by
    have hspos : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos (by norm_num))
    have hs2 : (eNorm b) ^ 2 ≠ 0 := ne_of_gt (by positivity)
    rw [hε]
    field_simp
  have hδeq : 2 / Real.sqrt 3 * (lam (Submodule.map (projScale b) L) (i - 1) + ε) / (eNorm b) ^ 2
      = 2 / Real.sqrt 3 * lam (Submodule.map (projScale b) L) (i - 1) / (eNorm b) ^ 2 + δ := by
    rw [mul_add, add_div, hεdiv]
  linarith

/-! ## The determinant of the scaled projection -/

private lemma dotZ_cast (u v : ι → ℤ) :
    ((dotZ u v : ℤ) : ℝ) = ∑ k, ((u k : ℤ) : ℝ) * ((v k : ℤ) : ℝ) := by
  simp only [dotZ, Int.cast_sum, Int.cast_mul]

private lemma dotZ_projScale_projScale (b x y : ι → ℤ) :
    dotZ (projScale b x) (projScale b y)
      = (dotZ b b) ^ 2 * dotZ x y - (dotZ b b) * (dotZ x b) * (dotZ y b) := by
  simp only [projScale_apply, dotZ_sub, dotZ_sub_right, dotZ_smul, dotZ_smul_right,
    dotZ_comm b y]
  ring

private lemma eNorm_sq_cast (b : ι → ℤ) : (eNorm b) ^ 2 = ((dotZ b b : ℤ) : ℝ) := eNorm_sq_eq b

private lemma gram_det_nonneg {m : ℕ} (w : Fin m → ι → ℝ) :
    0 ≤ (Matrix.of fun i j : Fin m => ∑ k, w i k * w j k).det := by
  have h : (Matrix.of fun i j : Fin m => ∑ k, w i k * w j k)
      = (Matrix.of fun (i : Fin m) (k : ι) => w i k)
        * (Matrix.of fun (i : Fin m) (k : ι) => w i k).transpose := by
    ext i j
    simp [Matrix.mul_apply]
  rw [h]
  have h2 : (Matrix.of fun (i : Fin m) (k : ι) => w i k)
        * (Matrix.of fun (i : Fin m) (k : ι) => w i k).transpose
      = (Matrix.conjTranspose ((Matrix.of fun (i : Fin m) (k : ι) => w i k).transpose))
        * (Matrix.of fun (i : Fin m) (k : ι) => w i k).transpose := by
    ext i j
    simp
  rw [h2]
  exact Matrix.PosSemidef.det_nonneg (Matrix.posSemidef_conjTranspose_mul_self _)

/-- **Schur complement identity** for the Gram matrix of a family with one distinguished vector. -/
private lemma det_gram_cons_aux {n : ℕ} (v : ι → ℝ) (u : Fin n → ι → ℝ)
    (hv : (∑ k, v k ^ 2) ≠ 0) :
    (Matrix.of fun i j : Fin (n + 1) =>
        ∑ k, ((Fin.cons v u : Fin (n + 1) → ι → ℝ) i) k
              * ((Fin.cons v u : Fin (n + 1) → ι → ℝ) j) k).det
      = (∑ k, v k ^ 2) *
        (Matrix.of fun i j : Fin n =>
          (∑ k, u i k * u j k)
            - (∑ k, v k * u i k) * (∑ k, v k * u j k) / (∑ k, v k ^ 2)).det := by
  classical
  set s : ℝ := ∑ k, v k ^ 2 with hs
  set y : Fin n → ℝ := fun j => ∑ k, v k * u j k with hy
  set D : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => ∑ k, u i k * u j k with hD
  set E : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun i j => (∑ k, u i k * u j k) - y i * y j / s with hE
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of fun i j =>
      ∑ k, ((Fin.cons v u : Fin (n + 1) → ι → ℝ) i) k
            * ((Fin.cons v u : Fin (n + 1) → ι → ℝ) j) k with hA
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j =>
    Fin.cases (Fin.cases s (fun _ => 0) j) (fun i' => Fin.cases (y i') (fun j' => E i' j') j) i
    with hB
  set U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j =>
    Fin.cases (Fin.cases (1 : ℝ) (fun j' => -y j' / s) j)
      (fun i' => Fin.cases 0 (fun j' => if i' = j' then (1 : ℝ) else 0) j) i with hU
  have hsne : s ≠ 0 := by rw [hs]; exact hv
  have hA00 : A 0 0 = s := by
    rw [hA]
    simp only [Matrix.of_apply, Fin.cons_zero]
    rw [hs]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have hA0j : ∀ j' : Fin n, A 0 j'.succ = y j' := by
    intro j'
    rw [hA, hy]
    simp only [Matrix.of_apply, Fin.cons_zero, Fin.cons_succ]
  have hAi0 : ∀ i' : Fin n, A i'.succ 0 = y i' := by
    intro i'
    rw [hA, hy]
    simp only [Matrix.of_apply, Fin.cons_zero, Fin.cons_succ]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have hAij : ∀ i' j' : Fin n, A i'.succ j'.succ = D i' j' := by
    intro i' j'
    rw [hA, hD]
    simp only [Matrix.of_apply, Fin.cons_succ]
  have hU00 : U 0 0 = 1 := by rw [hU]; simp
  have hU0j : ∀ j' : Fin n, U 0 j'.succ = -y j' / s := by intro j'; rw [hU]; simp
  have hUi0 : ∀ i' : Fin n, U i'.succ 0 = 0 := by intro i'; rw [hU]; simp
  have hUij : ∀ i' j' : Fin n, U i'.succ j'.succ = if i' = j' then (1 : ℝ) else 0 := by
    intro i' j'; rw [hU]; simp
  have hB00 : B 0 0 = s := by rw [hB]; simp
  have hB0j : ∀ j' : Fin n, B 0 j'.succ = 0 := by intro j'; rw [hB]; simp
  have hBi0 : ∀ i' : Fin n, B i'.succ 0 = y i' := by intro i'; rw [hB]; simp
  have hBij : ∀ i' j' : Fin n, B i'.succ j'.succ = E i' j' := by
    intro i' j'; rw [hB]; simp
  have hAU : A * U = B := by
    ext i j
    refine Fin.cases ?_ (fun i' => ?_) i
    · refine Fin.cases ?_ (fun j' => ?_) j
      · rw [Matrix.mul_apply, Fin.sum_univ_succ, hA00, hU00, hB00]
        rw [Finset.sum_eq_zero (fun t _ => by rw [hUi0 t, mul_zero]), add_zero, mul_one]
      · rw [Matrix.mul_apply, Fin.sum_univ_succ, hA00, hU0j j', hB0j j']
        rw [Finset.sum_eq_single j'
          (fun t _ ht => by rw [hA0j t, hUij t j', if_neg (fun h : t = j' => ht h), mul_zero])
          (fun h => absurd (Finset.mem_univ j') h)]
        rw [hA0j j', hUij j' j', if_pos rfl, mul_one]
        field_simp
        ring
    · refine Fin.cases ?_ (fun j' => ?_) j
      · rw [Matrix.mul_apply, Fin.sum_univ_succ, hAi0, hU00, hBi0]
        rw [Finset.sum_eq_zero (fun t _ => by rw [hUi0 t, mul_zero]), add_zero, mul_one]
      · rw [Matrix.mul_apply, Fin.sum_univ_succ, hAi0, hU0j j', hBij i' j']
        rw [Finset.sum_eq_single j'
          (fun t _ ht => by rw [hAij i' t, hUij t j', if_neg (fun h : t = j' => ht h), mul_zero])
          (fun h => absurd (Finset.mem_univ j') h)]
        rw [hAij i' j', hUij j' j', if_pos rfl, mul_one, hE, hD, hy]
        simp only [Matrix.of_apply]
        ring
  have hUdet : U.det = 1 := by
    rw [Matrix.det_succ_column_zero]
    have hzero : ∀ i : Fin (n + 1), i ≠ 0 →
        (-1) ^ (i : ℕ) * U i 0 * (U.submatrix i.succAbove Fin.succ).det = 0 := by
      intro i hi
      obtain ⟨m, hm⟩ := i
      cases m with
      | zero => exact absurd rfl hi
      | succ m' =>
        have h1 : U (⟨m' + 1, hm⟩ : Fin (n + 1)) 0 = 0 := hUi0 ⟨m', by omega⟩
        rw [h1, mul_zero, zero_mul]
    have hsub : U.submatrix (Fin.succAbove (0 : Fin (n + 1))) Fin.succ = 1 := by
      rw [Fin.succAbove_zero]
      ext i j
      rw [Matrix.submatrix_apply, hUij i j, Matrix.one_apply]
    have hidx : (((0 : Fin (n + 1)) : ℕ)) = 0 := rfl
    rw [Finset.sum_eq_single 0 (fun b _ hb => hzero b hb)
      (fun h => absurd (Finset.mem_univ 0) h)]
    calc (-1 : ℝ) ^ (((0 : Fin (n + 1)) : ℕ)) * U 0 0
          * (U.submatrix (Fin.succAbove (0 : Fin (n + 1))) Fin.succ).det
        = U 0 0 * (U.submatrix (Fin.succAbove (0 : Fin (n + 1))) Fin.succ).det := by
          rw [hidx, pow_zero, one_mul]
      _ = U 0 0 * (1 : Matrix (Fin n) (Fin n) ℝ).det := by rw [hsub]
      _ = 1 := by rw [Matrix.det_one, hU00, mul_one]
  have hBdet : B.det = s * E.det := by
    rw [Matrix.det_succ_row_zero]
    have hzero : ∀ j : Fin (n + 1), j ≠ 0 →
        (-1) ^ (j : ℕ) * B 0 j * (B.submatrix Fin.succ j.succAbove).det = 0 := by
      intro j hj
      obtain ⟨m, hm⟩ := j
      cases m with
      | zero => exact absurd rfl hj
      | succ m' =>
        have h1 : B 0 (⟨m' + 1, hm⟩ : Fin (n + 1)) = 0 := hB0j ⟨m', by omega⟩
        rw [h1, mul_zero, zero_mul]
    have hsub : B.submatrix (Fin.succAbove (0 : Fin (n + 1))) Fin.succ = E := by
      rw [Fin.succAbove_zero]
      ext i j
      rw [Matrix.submatrix_apply, hBij i j]
    have hidx : (((0 : Fin (n + 1)) : ℕ)) = 0 := rfl
    rw [Finset.sum_eq_single 0 (fun b _ hb => hzero b hb)
      (fun h => absurd (Finset.mem_univ 0) h)]
    calc (-1 : ℝ) ^ (((0 : Fin (n + 1)) : ℕ)) * B 0 0
          * (B.submatrix (Fin.succAbove (0 : Fin (n + 1))) Fin.succ).det
        = B 0 0 * (B.submatrix (Fin.succAbove (0 : Fin (n + 1))) Fin.succ).det := by
          rw [hidx, pow_zero, one_mul]
      _ = B 0 0 * E.det := by rw [hsub]
      _ = s * E.det := by rw [hB00]
  calc (Matrix.of fun i j : Fin (n + 1) =>
        ∑ k, ((Fin.cons v u : Fin (n + 1) → ι → ℝ) i) k
              * ((Fin.cons v u : Fin (n + 1) → ι → ℝ) j) k).det
      = A.det := by rw [hA]
    _ = A.det * U.det := by rw [hUdet, mul_one]
    _ = (A * U).det := (Matrix.det_mul A U).symm
    _ = B.det := by rw [hAU]
    _ = s * E.det := hBdet
    _ = (∑ k, v k ^ 2) *
        (Matrix.of fun i j : Fin n =>
          (∑ k, u i k * u j k)
            - (∑ k, v k * u i k) * (∑ k, v k * u j k) / (∑ k, v k ^ 2)).det := by
        rw [hs, hE, hy]

/-- `detL` of the image of the scaled projection: `detL (projScale b L) = ‖b‖ ^ (2 rk L - 3) detL L`
for a shortest vector `b` of `L` of rank at least two. -/
lemma detL_map_projScale_aux (L : Submodule ℤ (ι → ℤ)) {b : ι → ℤ} (hb : b ∈ L) (hb0 : b ≠ 0)
    (hmin : ∀ x ∈ L, x ≠ 0 → eNorm b ≤ eNorm x) (hr : 2 ≤ rk L) :
    detL (Submodule.map (projScale b) L) = (eNorm b) ^ (2 * rk L - 3) * detL L := by
  classical
  have hker : LinearMap.ker (projScale b) ⊓ L = Submodule.span ℤ {b} :=
    ker_projScale_inf_aux L hb hb0 hmin
  have hrk : rk (Submodule.map (projScale b) L) = rk L - 1 :=
    rk_map_projScale_aux L hb hb0 hmin
  obtain ⟨n', e'⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) (Submodule.map (projScale b) L)
  have hn' : n' = rk L - 1 := by
    rw [← hrk]
    show n' = Module.finrank ℤ ↥(Submodule.map (projScale b) L)
    rw [Module.finrank_eq_card_basis e']
    simp
  have hlift : ∀ j : Fin n', ∃ x ∈ L, projScale b x = (e' j : ι → ℤ) :=
    fun j => Submodule.mem_map.mp (e' j).2
  let xl : Fin n' → ι → ℤ := fun j => Classical.choose (hlift j)
  have hxlL : ∀ j, xl j ∈ L := fun j => (Classical.choose_spec (hlift j)).1
  have hxlT : ∀ j, projScale b (xl j) = (e' j : ι → ℤ) :=
    fun j => (Classical.choose_spec (hlift j)).2
  let c : Fin (n' + 1) → L := Fin.cons (⟨b, hb⟩ : L) (fun j => (⟨xl j, hxlL j⟩ : L))
  have hc0 : c 0 = (⟨b, hb⟩ : L) := by simp [c]
  have hcs : ∀ j : Fin n', c j.succ = (⟨xl j, hxlL j⟩ : L) := fun j => by simp [c]
  have hker' : ∀ x : L, (projScale b) (x : ι → ℤ) = 0 → x ∈ Submodule.span ℤ {(⟨b, hb⟩ : L)} := by
    intro x hx
    have hx1 : (x : ι → ℤ) ∈ LinearMap.ker (projScale b) ⊓ L := ⟨hx, x.2⟩
    rw [hker, Submodule.mem_span_singleton] at hx1
    obtain ⟨m, hm⟩ := hx1
    exact Submodule.mem_span_singleton.mpr ⟨m, Subtype.ext (by simpa using hm)⟩
  have hcli : LinearIndependent ℤ c := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have hcoe : (∑ k : Fin (n' + 1), a k • ((c k : L) : ι → ℤ))
        = ((∑ k, a k • c k : L) : ι → ℤ) := by simp
    have h2 : (projScale b) (∑ k : Fin (n' + 1), a k • ((c k : L) : ι → ℤ)) = 0 := by
      rw [hcoe, ha, Submodule.coe_zero, map_zero]
    rw [map_sum, Fin.sum_univ_succ] at h2
    have h3 : (projScale b) (a 0 • ((c 0 : L) : ι → ℤ)) = 0 := by
      rw [hc0, map_smul, show (projScale b) b = 0 from by rw [projScale_apply, sub_self],
        smul_zero]
    have h4 : (∑ j : Fin n', (projScale b) (a j.succ • ((c j.succ : L) : ι → ℤ)))
        = ∑ j : Fin n', a j.succ • ((e' j : ↥(Submodule.map (projScale b) L)) : ι → ℤ) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hcs j, map_smul, hxlT j]
    rw [h3, zero_add, h4] at h2
    have he'LI : LinearIndependent ℤ
        (fun j : Fin n' => ((e' j : ↥(Submodule.map (projScale b) L)) : ι → ℤ)) :=
      e'.linearIndependent.map' (Submodule.map (projScale b) L).subtype (Submodule.ker_subtype _)
    have h5 : ∀ j : Fin n', a j.succ = 0 :=
      fun j => (Fintype.linearIndependent_iff.mp he'LI) (fun j => a j.succ) h2 j
    have h6 : a 0 • (⟨b, hb⟩ : L) = 0 := by
      have h7 := ha
      rw [Fin.sum_univ_succ] at h7
      have h8 : (∑ j : Fin n', a j.succ • c j.succ) = 0 :=
        Finset.sum_eq_zero (fun j _ => by rw [h5 j, zero_smul])
      rw [h8, add_zero] at h7
      rwa [hc0] at h7
    have h9 : a 0 = 0 := by
      rcases smul_eq_zero.mp h6 with h | h
      · exact h
      · exact absurd h (by simpa using hb0)
    intro k
    exact Fin.cases h9 (fun j => h5 j) k
  have hcsp : ⊤ ≤ Submodule.span ℤ (Set.range c) := by
    intro z _
    have hzL' : (projScale b) (z : ι → ℤ) ∈ Submodule.map (projScale b) L := ⟨z, z.2, rfl⟩
    set t : ↥(Submodule.map (projScale b) L) := ⟨(projScale b) (z : ι → ℤ), hzL'⟩ with ht
    have hrepr : ((∑ j : Fin n', (e'.repr t j) • e' j : ↥(Submodule.map (projScale b) L))
        : ι → ℤ) = (projScale b) (z : ι → ℤ) := by
      rw [e'.sum_repr t]
    have hmem : (∑ j : Fin n', (e'.repr t j) • c j.succ) ∈ Submodule.span ℤ (Set.range c) :=
      Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self j.succ)))
    have hdiff : z - ∑ j : Fin n', (e'.repr t j) • c j.succ ∈ Submodule.span ℤ (Set.range c) := by
      have hproj : (projScale b)
          ((z - ∑ j : Fin n', (e'.repr t j) • c j.succ : L) : ι → ℤ) = 0 := by
        have hcoesum : ((∑ j : Fin n', (e'.repr t j) • c j.succ : L) : ι → ℤ)
            = ∑ j : Fin n', (e'.repr t j) • ((c j.succ : L) : ι → ℤ) := by simp
        rw [Submodule.coe_sub, hcoesum, map_sub, map_sum]
        have h0 : (∑ j : Fin n', (projScale b) ((e'.repr t j) • ((c j.succ : L) : ι → ℤ)))
            = (projScale b) (z : ι → ℤ) := by
          rw [← hrepr]
          simp only [Submodule.coe_sum, Submodule.coe_smul]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [hcs j, map_smul, hxlT j]
        rw [h0, sub_self]
      have hb_mem : z - ∑ j : Fin n', (e'.repr t j) • c j.succ
          ∈ Submodule.span ℤ {(⟨b, hb⟩ : L)} := hker' _ hproj
      have hsub : Submodule.span ℤ {(⟨b, hb⟩ : L)} ≤ Submodule.span ℤ (Set.range c) :=
        Submodule.span_le.mpr (by rintro _ rfl; exact Submodule.subset_span ⟨0, hc0.symm⟩)
      exact hsub hb_mem
    rw [(sub_add_cancel z (∑ j : Fin n', (e'.repr t j) • c j.succ)).symm]
    exact Submodule.add_mem _ hdiff hmem
  let cb : Module.Basis (Fin (n' + 1)) ℤ L := Module.Basis.mk hcli hcsp
  -- the two Gram matrices
  have hdetL : detL L = Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (n' + 1) =>
      ∑ x, (((cb i : ↥L) : ι → ℤ) x : ℝ) * (((cb j : ↥L) : ι → ℤ) x : ℝ))) :=
    Work.HP.Lat.detL_basis_gram L cb
  have hdetL' : detL (Submodule.map (projScale b) L)
      = Real.sqrt (Matrix.det (Matrix.of fun i j : Fin n' =>
        ∑ x, (((e' i : ↥(Submodule.map (projScale b) L)) : ι → ℤ) x : ℝ)
              * (((e' j : ↥(Submodule.map (projScale b) L)) : ι → ℤ) x : ℝ))) :=
    Work.HP.Lat.detL_basis_gram (Submodule.map (projScale b) L) e'
  set v : ι → ℝ := fun k => ((b k : ℤ) : ℝ) with hv
  set u : Fin n' → ι → ℝ := fun j k => ((xl j k : ℤ) : ℝ) with hu
  set s2 : ℝ := ∑ k, v k ^ 2 with hs2def
  have hs2 : s2 = (eNorm b) ^ 2 := by
    rw [hs2def, hv, eNorm_sq_eq, dotZ_apply]
    push_cast
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have hvne : (∑ k, v k ^ 2) ≠ 0 := by
    rw [← hs2def, hs2]
    exact pow_ne_zero _ (ne_of_gt (eNorm_pos_of_ne_zero hb0))
  have hs2ne : s2 ≠ 0 := by rw [hs2]; exact pow_ne_zero _ (ne_of_gt (eNorm_pos_of_ne_zero hb0))
  have hSchur := det_gram_cons_aux v u hvne
  -- the family `c` is the `cons` family
  have hfam : ∀ i : Fin (n' + 1), (fun x => (((cb i : ↥L) : ι → ℤ) x : ℝ))
      = (Fin.cons v u : Fin (n' + 1) → ι → ℝ) i := by
    intro i
    dsimp only [cb, c]
    refine Fin.cases ?_ ?_ i
    · funext x
      simp only [Module.Basis.mk_apply, hv, Fin.cons_zero]
    · intro i'
      funext x
      simp only [Module.Basis.mk_apply, hu, Fin.cons_succ]
  have hAv : (Matrix.of fun i j : Fin (n' + 1) =>
        ∑ x, (((cb i : ↥L) : ι → ℤ) x : ℝ) * (((cb j : ↥L) : ι → ℤ) x : ℝ))
      = (Matrix.of fun i j : Fin (n' + 1) =>
        ∑ x, ((Fin.cons v u : Fin (n' + 1) → ι → ℝ) i) x
              * ((Fin.cons v u : Fin (n' + 1) → ι → ℝ) j) x) := by
    ext i j
    rw [Matrix.of_apply, Matrix.of_apply, ← hfam i, ← hfam j]
  have hGc : (Matrix.of fun i j : Fin (n' + 1) =>
        ∑ x, (((cb i : ↥L) : ι → ℤ) x : ℝ) * (((cb j : ↥L) : ι → ℤ) x : ℝ)).det
      = (detL L) ^ 2 := by
    rw [hdetL]
    exact (Real.sq_sqrt (gram_det_nonneg (fun i x => (((cb i : ↥L) : ι → ℤ) x : ℝ)))).symm
  -- the Schur complement written in terms of the Gram matrix of `e'`
  set y : Fin n' → ℝ := fun j => ∑ k, v k * u j k with hy
  set E : Matrix (Fin n') (Fin n') ℝ :=
    Matrix.of fun i j => (∑ k, u i k * u j k) - y i * y j / s2 with hE
  have hSchurGc : s2 * E.det = (Matrix.of fun i j : Fin (n' + 1) =>
        ∑ x, (((cb i : ↥L) : ι → ℤ) x : ℝ) * (((cb j : ↥L) : ι → ℤ) x : ℝ)).det := by
    rw [hAv, hSchur]
  have hN : ((dotZ b b : ℤ) : ℝ) = s2 := by
    rw [dotZ_cast, hs2def, hv]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have hDij : ∀ i j : Fin n', ((dotZ (xl i) (xl j) : ℤ) : ℝ) = ∑ k, u i k * u j k := by
    intro i j
    rw [dotZ_cast, hu]
  have hyi : ∀ i : Fin n', ((dotZ (xl i) b : ℤ) : ℝ) = y i := by
    intro i
    rw [dotZ_cast, hy]
    simp only [hu, hv]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have hGe : (Matrix.of fun i j : Fin n' =>
        ∑ x, (((e' i : ↥(Submodule.map (projScale b) L)) : ι → ℤ) x : ℝ)
              * (((e' j : ↥(Submodule.map (projScale b) L)) : ι → ℤ) x : ℝ))
      = (s2 ^ 2) • E := by
    ext i j
    rw [Matrix.smul_apply, hE, Matrix.of_apply, Matrix.of_apply, smul_eq_mul,
      ← hxlT i, ← hxlT j,
      ← dotZ_cast (projScale b (xl i)) (projScale b (xl j)), dotZ_projScale_projScale]
    push_cast
    rw [hN, hDij i j, hyi i, hyi j]
    field_simp
  have hGedet : (Matrix.of fun i j : Fin n' =>
        ∑ x, (((e' i : ↥(Submodule.map (projScale b) L)) : ι → ℤ) x : ℝ)
              * (((e' j : ↥(Submodule.map (projScale b) L)) : ι → ℤ) x : ℝ)).det
      = (s2 ^ 2) ^ n' * E.det := by
    rw [hGe, Matrix.det_smul, Fintype.card_fin]
  have hexp2 : (s2 ^ 2) ^ n' = ((eNorm b) ^ (2 * n' - 1)) ^ 2 * s2 := by
    have h2n : 1 ≤ 2 * n' := by omega
    have hL : (s2 ^ 2) ^ n' = (eNorm b) ^ (4 * n') := by
      rw [hs2, ← pow_mul, ← pow_mul]
      congr 1
      ring
    have hR : ((eNorm b) ^ (2 * n' - 1)) ^ 2 * s2 = (eNorm b) ^ (4 * n') := by
      rw [hs2, ← pow_mul, ← pow_add]
      congr 1
      omega
    rw [hL, hR]
  have hdetGe : (Matrix.of fun i j : Fin n' =>
        ∑ x, (((e' i : ↥(Submodule.map (projScale b) L)) : ι → ℤ) x : ℝ)
              * (((e' j : ↥(Submodule.map (projScale b) L)) : ι → ℤ) x : ℝ)).det
      = ((eNorm b) ^ (2 * n' - 1)) ^ 2 * (detL L) ^ 2 := by
    calc (Matrix.of fun i j : Fin n' =>
          ∑ x, (((e' i : ↥(Submodule.map (projScale b) L)) : ι → ℤ) x : ℝ)
                * (((e' j : ↥(Submodule.map (projScale b) L)) : ι → ℤ) x : ℝ)).det
        = (s2 ^ 2) ^ n' * E.det := hGedet
      _ = (((eNorm b) ^ (2 * n' - 1)) ^ 2 * s2) * E.det := by rw [hexp2]
      _ = ((eNorm b) ^ (2 * n' - 1)) ^ 2 * (s2 * E.det) := by rw [mul_assoc]
      _ = ((eNorm b) ^ (2 * n' - 1)) ^ 2 * (detL L) ^ 2 := by rw [hSchurGc, hGc]
  have h2n' : 2 * n' - 1 = 2 * rk L - 3 := by omega
  calc detL (Submodule.map (projScale b) L)
      = Real.sqrt ((Matrix.of fun i j : Fin n' =>
          ∑ x, (((e' i : ↥(Submodule.map (projScale b) L)) : ι → ℤ) x : ℝ)
                * (((e' j : ↥(Submodule.map (projScale b) L)) : ι → ℤ) x : ℝ)).det) := hdetL'
    _ = Real.sqrt ((((eNorm b) ^ (2 * n' - 1)) ^ 2) * (detL L) ^ 2) := by rw [hdetGe]
    _ = (eNorm b) ^ (2 * n' - 1) * detL L := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg (eNorm_nonneg b) _),
          Real.sqrt_sq (detL_nonneg L)]
    _ = (eNorm b) ^ (2 * rk L - 3) * detL L := by rw [h2n']

theorem minkowski_prod {ι : Type} [Fintype ι] [DecidableEq ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ L : Submodule ℤ (ι → ℤ),
      (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ K * detL L := by
  set C : ℝ := 2 / Real.sqrt 3 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hC1 : 1 ≤ C := by
    rw [hCdef, le_div_iff₀ (Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 3))]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
  refine ⟨C ^ (Fintype.card ι * Fintype.card ι), by positivity, ?_⟩
  intro L
  have hrkbot : rk (⊥ : Submodule ℤ (ι → ℤ)) = 0 := by
    rw [rk]; exact Submodule.finrank_eq_zero.mpr rfl
  have hcard : rk L ≤ Fintype.card ι := by
    rw [rk]
    refine (Submodule.finrank_le L).trans ?_
    rw [Module.finrank_fintype_fun_eq_card]
  have key : ∀ r : ℕ, ∀ L : Submodule ℤ (ι → ℤ), rk L ≤ r →
      (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ C ^ (rk L * rk L) * detL L := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro L hL
      rcases Nat.lt_or_ge (rk L) 2 with h2 | h2
      · have hb := minkowski_base_aux L (by omega)
        calc (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ detL L := hb
          _ ≤ C ^ (rk L * rk L) * detL L := by
              have h1 : (1:ℝ) ≤ C ^ (rk L * rk L) := one_le_pow₀ hC1
              nlinarith [detL_nonneg L]
      · have hne : L ≠ ⊥ := by
          intro hbot
          rw [hbot, hrkbot] at h2
          omega
        obtain ⟨b, hbL, hb0, hbnorm, hbmin⟩ := exists_shortest_aux L hne
        set L' : Submodule ℤ (ι → ℤ) := Submodule.map (projScale b) L with hL'def
        have hrkL' : rk L' = rk L - 1 := rk_map_projScale_aux L hbL hb0 hbmin
        have hdet : detL L' = eNorm b ^ (2 * rk L - 3) * detL L :=
          detL_map_projScale_aux L hbL hb0 hbmin (by omega)
        have hIH : (∏ j ∈ Finset.range (rk L'), lam L' (j + 1))
            ≤ C ^ (rk L' * rk L') * detL L' := ih (rk L') (by omega) L' le_rfl
        rw [hrkL'] at hIH
        have hsplit : (∏ j ∈ Finset.range (rk L), lam L (j + 1))
            = eNorm b * ∏ j ∈ Finset.range (rk L - 1), lam L (j + 2) := by
          have hsucc : rk L - 1 + 1 = rk L := by omega
          have h1 : (∏ j ∈ Finset.range (rk L), lam L (j + 1))
              = (∏ j ∈ Finset.range (rk L - 1), lam L (j + 2)) * lam L 1 := by
            conv_lhs => rw [← hsucc, Finset.prod_range_succ']
          rw [h1, ← hbnorm, mul_comm]
        have hfac : ∀ j ∈ Finset.range (rk L - 1),
            lam L (j + 2) ≤ C * lam L' (j + 1) / (eNorm b) ^ 2 := by
          intro j hj
          have hj' : j + 2 ≤ rk L := by simp at hj; omega
          have := lam_projScale_le_aux L hbL hb0 hbmin (i := j + 2) (by omega) hj'
          rw [hCdef]
          simpa using this
        have hprod2 : (∏ j ∈ Finset.range (rk L - 1), lam L (j + 2))
            ≤ ∏ j ∈ Finset.range (rk L - 1), (C * lam L' (j + 1) / (eNorm b) ^ 2) :=
          Finset.prod_le_prod₀ (fun j _ => lam_nonneg L (j + 2)) hfac
        have hprod3 : (∏ j ∈ Finset.range (rk L - 1), (C * lam L' (j + 1) / (eNorm b) ^ 2))
            = C ^ (rk L - 1) * (∏ j ∈ Finset.range (rk L - 1), lam L' (j + 1))
              / (eNorm b) ^ (2 * (rk L - 1)) := by
          rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
            ← pow_mul]
          simp only [Finset.card_range]
        have hℓpos : 0 < eNorm b := eNorm_pos_of_ne_zero hb0
        have hQ' : (∏ j ∈ Finset.range (rk L - 1), lam L' (j + 1))
            ≤ C ^ ((rk L - 1) * (rk L - 1)) * (eNorm b ^ (2 * rk L - 3) * detL L) := by
          rw [← hdet]; exact hIH
        have hstep1 : eNorm b * (C ^ (rk L - 1) *
              (∏ j ∈ Finset.range (rk L - 1), lam L' (j + 1)) / (eNorm b) ^ (2 * (rk L - 1)))
            ≤ eNorm b * (C ^ (rk L - 1) * (C ^ ((rk L - 1) * (rk L - 1)) *
                (eNorm b ^ (2 * rk L - 3) * detL L)) / (eNorm b) ^ (2 * (rk L - 1))) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hℓpos)
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hQ' (by positivity)
        have hEq : eNorm b * (C ^ (rk L - 1) * (C ^ ((rk L - 1) * (rk L - 1)) *
                (eNorm b ^ (2 * rk L - 3) * detL L)) / (eNorm b) ^ (2 * (rk L - 1)))
            = C ^ ((rk L - 1) + (rk L - 1) * (rk L - 1)) * detL L := by
          have hℓne : eNorm b ≠ 0 := ne_of_gt hℓpos
          have hkey1 : eNorm b * eNorm b ^ (2 * rk L - 3) = eNorm b ^ (2 * (rk L - 1)) := by
            rw [← pow_succ']; congr 1; omega
          repeat rw [← mul_div_assoc]
          rw [div_eq_iff (pow_ne_zero _ hℓne)]
          rw [← mul_assoc (C ^ (rk L - 1)) (C ^ ((rk L - 1) * (rk L - 1))), ← pow_add]
          linear_combination (C ^ ((rk L - 1) + (rk L - 1) * (rk L - 1)) * detL L) * hkey1
        have hexp : (rk L - 1) + (rk L - 1) * (rk L - 1) ≤ rk L * rk L := by
          nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ rk L)]
        calc (∏ j ∈ Finset.range (rk L), lam L (j + 1))
            = eNorm b * ∏ j ∈ Finset.range (rk L - 1), lam L (j + 2) := hsplit
          _ ≤ eNorm b * ∏ j ∈ Finset.range (rk L - 1), (C * lam L' (j + 1) / (eNorm b) ^ 2) := by
              exact mul_le_mul_of_nonneg_left hprod2 (le_of_lt hℓpos)
          _ = eNorm b * (C ^ (rk L - 1) * (∏ j ∈ Finset.range (rk L - 1), lam L' (j + 1))
                  / (eNorm b) ^ (2 * (rk L - 1))) := by rw [hprod3]
          _ ≤ C ^ ((rk L - 1) + (rk L - 1) * (rk L - 1)) * detL L := hstep1.trans (le_of_eq hEq)
          _ ≤ C ^ (rk L * rk L) * detL L :=
              mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC1 hexp) (detL_nonneg L)
  have hle := key (Fintype.card ι) L hcard
  refine le_trans hle ?_
  have hle2 : C ^ (rk L * rk L) ≤ C ^ (Fintype.card ι * Fintype.card ι) :=
    pow_le_pow_right₀ hC1 (by nlinarith [hcard])
  exact mul_le_mul_of_nonneg_right hle2 (detL_nonneg L)

end Work.HP.numaux
