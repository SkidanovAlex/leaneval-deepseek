import Mathlib
import Submission.Work.Pi6.MSS.AssembleCore
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The Leibniz rule for the product on the pages of the multiplicative Serre spectral sequence

This file proves `Work.Pi6.MSS.mssMulLeib`, the Leibniz rule for the concrete product `mssMul`
and the differential `mssD` of the bidegree-indexed pages `mssE` built in
`Submission/Work/Pi6/MSS/AssembleCore.lean`.

The proof is a transfer of the `ℕ`-indexed Leibniz rule `pd_mul_leib`
(`Submission/Work/Pi6/MSS/pagesData.lean`) along the index equalities
`EI (a + b) = EI a + EI b`, `EN (a + b) = EN a + EN b`, `EI (a + vr r) = EI a + r`,
`EN (a + vr r) = EN a + 1`, using the cast toolkit developed below.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits
open Classical
attribute [local instance] Classical.propDecidable

noncomputable section

variable {𝕜 : Type} [Field 𝕜] {W : CohFilt 𝕜}

/-! ## 1. The cast toolkit -/

/-- `pEcast` depends on the index equalities only through their statements. -/
theorem pEcast_hom_congr {r s s' n n' : ℕ} (h1 h1' : s = s') (h2 h2' : n = n') :
    (pEcast 𝕜 W r h1 h2).hom = (pEcast 𝕜 W r h1' h2').hom := by
  rw [Subsingleton.elim h1 h1', Subsingleton.elim h2 h2']

theorem pEcast_hom_apply_congr {r s s' n n' : ℕ} (h1 h1' : s = s') (h2 h2' : n = n')
    (u : pEraw 𝕜 W r s n) :
    (pEcast 𝕜 W r h1 h2).hom u = (pEcast 𝕜 W r h1' h2').hom u := by
  rw [pEcast_hom_congr h1 h1' h2 h2']

/-- The composite of two `pEcast`s is a `pEcast`. -/
theorem pEcast_hom_apply_comp {r s1 s2 s3 n1 n2 n3 : ℕ} (h1 : s1 = s2) (h1' : s2 = s3)
    (h2 : n1 = n2) (h2' : n2 = n3) (u : pEraw 𝕜 W r s1 n1) :
    (pEcast 𝕜 W r h1' h2').hom ((pEcast 𝕜 W r h1 h2).hom u)
      = (pEcast 𝕜 W r (h1.trans h1') (h2.trans h2')).hom u := by
  cases h1; cases h1'; cases h2; cases h2'
  simp [pEcast, eqToIso_refl]

theorem pEcast_hom_add {r s s' n n' : ℕ} (h1 : s = s') (h2 : n = n')
    (u v : pEraw 𝕜 W r s n) :
    (pEcast 𝕜 W r h1 h2).hom (u + v)
      = (pEcast 𝕜 W r h1 h2).hom u + (pEcast 𝕜 W r h1 h2).hom v :=
  map_add (pEcast 𝕜 W r h1 h2).hom.hom u v

theorem pEcast_hom_smul {r s s' n n' : ℕ} (h1 : s = s') (h2 : n = n') (c : 𝕜)
    (u : pEraw 𝕜 W r s n) :
    (pEcast 𝕜 W r h1 h2).hom (c • u) = c • (pEcast 𝕜 W r h1 h2).hom u :=
  map_smul (pEcast 𝕜 W r h1 h2).hom.hom c u

theorem pCast_self {r s n : ℕ} (h1 : s = s) (h2 : n = n) (u : pEraw 𝕜 W r s n) :
    pCast 𝕜 W r h1 h2 u = u := by
  rw [Subsingleton.elim h1 rfl, Subsingleton.elim h2 rfl, pCast_apply_self]

theorem pCast_eq_pEcast_apply {r s s' n n' : ℕ} (h1 : s = s') (h2 : n = n')
    (u : pEraw 𝕜 W r s n) :
    pCast 𝕜 W r h1 h2 u = (pEcast 𝕜 W r h1 h2).hom u := by
  cases h1; cases h2
  rw [pEcast_hom_id, pCast_self]
  simp

theorem mssCast_apply {r : ℕ} {x y : ℤ × ℤ} (h : x = y) (v : mssE 𝕜 W r x) :
    (mssCast 𝕜 W r h) v = (pEcast 𝕜 W r (congrArg EI h) (congrArg EN h)).hom v := by
  cases h
  rw [mssCast_rfl, pEcast_hom_id]
  simp

theorem mssCast_self {r : ℕ} {x : ℤ × ℤ} (h : x = x) : mssCast 𝕜 W r h = LinearMap.id := by
  rw [Subsingleton.elim h rfl, mssCast_rfl]

/-- The product on the page `E_r^{a+b}` in the diagonal case is the concrete page product. -/
theorem mssMul_self_apply {r : ℕ} {a b : ℤ × ℤ} (hh : a + b = a + b)
    (x : mssE 𝕜 W r a) (y : mssE 𝕜 W r b) :
    mssMul 𝕜 W r a b (a + b) hh x y = mssMulRaw 𝕜 W r a b x y := by
  rw [show mssMul 𝕜 W r a b (a + b) hh = mssMulRaw 𝕜 W r a b from by
    rw [mssMul, mssCast_self]
    rw [show (LinearMap.llcomp 𝕜 (mssE 𝕜 W r b) (mssE 𝕜 W r (a+b)) (mssE 𝕜 W r (a+b)))
          LinearMap.id = LinearMap.id from by ext; simp [LinearMap.llcomp_apply]]
    simp]

theorem mssMulRaw_apply_enn {r : ℕ} {a b : ℤ × ℤ} (ha : Enn a) (hb : Enn b)
    (x : mssE 𝕜 W r a) (y : mssE 𝕜 W r b) :
    mssMulRaw 𝕜 W r a b x y
      = (pEcast 𝕜 W r (EI_add ha hb) (EN_add ha hb)).hom
          (pd_mul r (EI a) (EN a) (EI b) (EN b) x y) := by
  rw [show mssMulRaw 𝕜 W r a b x y
      = (pCast 𝕜 W r (EI_add ha hb) (EN_add ha hb))
          (pd_mul r (EI a) (EN a) (EI b) (EN b) x y) from by
      simp only [mssMulRaw_pos (𝕜 := 𝕜) (W := W) (r := r) ha hb, mssMulStep,
        LinearMap.comp_apply, LinearMap.llcomp_apply],
    pCast_eq_pEcast_apply]

theorem mssMulRaw_apply_neg {r : ℕ} {a b : ℤ × ℤ} (ha : ¬ Enn a)
    (x : mssE 𝕜 W r a) (y : mssE 𝕜 W r b) : mssMulRaw 𝕜 W r a b x y = 0 := by
  rw [mssMulRaw_neg (𝕜 := 𝕜) (W := W) (r := r) ha, LinearMap.zero_apply,
    LinearMap.zero_apply]

theorem mssMulRaw_apply_neg' {r : ℕ} {a b : ℤ × ℤ} (ha : Enn a) (hb : ¬ Enn b)
    (x : mssE 𝕜 W r a) (y : mssE 𝕜 W r b) : mssMulRaw 𝕜 W r a b x y = 0 := by
  rw [mssMulRaw_neg' (𝕜 := 𝕜) (W := W) (r := r) ha hb, LinearMap.zero_apply,
    LinearMap.zero_apply]

theorem mssD_apply_enn {r : ℕ} {a : ℤ × ℤ} (ha : Enn a) (ha' : Enn (a + Work.Pi6.vr r))
    (x : mssE 𝕜 W r a) :
    (mssD 𝕜 W r a (a + Work.Pi6.vr r)).hom x
      = (pEcast 𝕜 W r (EI_add_vr r ha ha') (EN_add_vr r ha)).hom
          ((pD 𝕜 W r (EI a) (EN a)).hom x) := by
  rw [mssD_self, mssDMain_pos 𝕜 W r ha ha', mssDStep]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]

theorem mssD_apply_neg {r : ℕ} {a : ℤ × ℤ} (ha : Enn a) (ha' : ¬ Enn (a + Work.Pi6.vr r))
    (x : mssE 𝕜 W r a) :
    (mssD 𝕜 W r a (a + Work.Pi6.vr r)).hom x = 0 := by
  rw [mssD_self, mssDMain_pos_neg 𝕜 W r ha ha', ModuleCat.hom_zero,
    LinearMap.zero_apply]

theorem pD_pEcast_apply {r s s' n n' : ℕ} (h1 : s = s') (h2 : n = n')
    (v : pEraw 𝕜 W r s n) :
    (pD 𝕜 W r s' n').hom ((pEcast 𝕜 W r h1 h2).hom v)
      = (pEcast 𝕜 W r (congrArg (· + r) h1) (congrArg (· + 1) h2)).hom
          ((pD 𝕜 W r s n).hom v) := by
  cases h1; cases h2
  rw [pEcast_hom_id, pEcast_hom_id]
  simp

theorem pd_mul_pEcast_left {r s n s1 n1 s2 n2 : ℕ} (h1 : s = s1) (h2 : n = n1)
    (u : pEraw 𝕜 W r s n) (y : pEraw 𝕜 W r s2 n2) :
    (pd_mul r s1 n1 s2 n2) ((pEcast 𝕜 W r h1 h2).hom u) y
      = (pEcast 𝕜 W r (congrArg (· + s2) h1) (congrArg (· + n2) h2)).hom
          ((pd_mul r s n s2 n2) u y) := by
  cases h1; cases h2
  rw [pEcast_hom_id, pEcast_hom_id]
  simp

theorem pd_mul_pEcast_right {r s n s1 n1 s2 n2 : ℕ} (h1 : s2 = s1) (h2 : n2 = n1)
    (u : pEraw 𝕜 W r s n) (w : pEraw 𝕜 W r s2 n2) :
    (pd_mul r s n s1 n1) u ((pEcast 𝕜 W r h1 h2).hom w)
      = (pEcast 𝕜 W r (congrArg (s + ·) h1) (congrArg (n + ·) h2)).hom
          ((pd_mul r s n s2 n2) u w) := by
  cases h1; cases h2
  rw [pEcast_hom_id, pEcast_hom_id]
  simp

/-- The product of two elements of the first quadrant, in terms of `pd_mul`. -/
theorem mssMul_apply_enn {r : ℕ} {a b c : ℤ × ℤ} (ha : Enn a) (hb : Enn b) (h : a + b = c)
    (x : mssE 𝕜 W r a) (y : mssE 𝕜 W r b) :
    mssMul 𝕜 W r a b c h x y
      = (pEcast 𝕜 W r (congrArg EI h) (congrArg EN h)).hom
          ((pEcast 𝕜 W r (EI_add ha hb) (EN_add ha hb)).hom
            (pd_mul r (EI a) (EN a) (EI b) (EN b) x y)) := by
  rw [show mssMul 𝕜 W r a b c h x y
      = (mssCast 𝕜 W r h) ((pCast 𝕜 W r (EI_add ha hb) (EN_add ha hb))
          (pd_mul r (EI a) (EN a) (EI b) (EN b) x y)) from by
      simp only [mssMul, mssMulRaw_pos (𝕜 := 𝕜) (W := W) (r := r) ha hb, mssMulStep,
        LinearMap.comp_apply, LinearMap.llcomp_apply],
    mssCast_apply, pCast_eq_pEcast_apply]

theorem mssMul_eq_zero_left {r : ℕ} {a b c : ℤ × ℤ} (h : a + b = c) (ha : ¬ Enn a) :
    mssMul 𝕜 W r a b c h = 0 := by
  apply LinearMap.ext; intro x
  apply LinearMap.ext; intro y
  rw [show mssMul 𝕜 W r a b c h x y
      = (mssCast 𝕜 W r h) (mssMulRaw 𝕜 W r a b x y) from by
      simp only [mssMul, LinearMap.comp_apply, LinearMap.llcomp_apply]]
  simp [mssMulRaw_apply_neg (𝕜 := 𝕜) (W := W) (r := r) ha x y]

theorem mssMulRaw_eq_zero_right {r : ℕ} {a b : ℤ × ℤ} (hb : ¬ Enn b) :
    mssMulRaw 𝕜 W r a b = 0 := by
  by_cases ha : Enn a
  · rw [mssMulRaw_neg' (𝕜 := 𝕜) (W := W) (r := r) ha hb]
  · rw [mssMulRaw_neg (𝕜 := 𝕜) (W := W) (r := r) ha]

theorem mssMul_eq_zero_right {r : ℕ} {a b c : ℤ × ℤ} (h : a + b = c) (hb : ¬ Enn b) :
    mssMul 𝕜 W r a b c h = 0 := by
  apply LinearMap.ext; intro x
  apply LinearMap.ext; intro y
  rw [show mssMul 𝕜 W r a b c h x y
      = (mssCast 𝕜 W r h) (mssMulRaw 𝕜 W r a b x y) from by
      simp only [mssMul, LinearMap.comp_apply, LinearMap.llcomp_apply]]
  simp [mssMulRaw_eq_zero_right (𝕜 := 𝕜) (W := W) (r := r) hb]

theorem mssMul_apply_zero_left {r : ℕ} {a b c : ℤ × ℤ} (h : a + b = c)
    (y : mssE 𝕜 W r b) : mssMul 𝕜 W r a b c h 0 y = 0 := by
  simp

theorem mssMul_apply_zero_right {r : ℕ} {a b c : ℤ × ℤ} (h : a + b = c)
    (x : mssE 𝕜 W r a) : mssMul 𝕜 W r a b c h x 0 = 0 := by
  simp

/-! ## 2. The Leibniz rule in the completely non-degenerate case -/

/-- Leibniz for `mssD`/`mssMul`, assuming that `a`, `b`, `a + vr r` and `b + vr r` are all in
the first quadrant. -/
theorem mssMulLeib_enn (r : ℕ) (hr : 2 ≤ r)
    (a b : ℤ × ℤ) (ha : Enn a) (hb : Enn b) (hA : Enn (a + Work.Pi6.vr r))
    (hB : Enn (b + Work.Pi6.vr r)) (hh : a + b = a + b)
    (h1 : (a + Work.Pi6.vr r) + b = (a + b) + Work.Pi6.vr r)
    (h2 : a + (b + Work.Pi6.vr r) = (a + b) + Work.Pi6.vr r)
    (x : mssE 𝕜 W r a) (y : mssE 𝕜 W r b) :
    (mssD 𝕜 W r (a + b) ((a + b) + Work.Pi6.vr r)).hom
        (mssMul 𝕜 W r a b (a + b) hh x y)
      = mssMul 𝕜 W r (a + Work.Pi6.vr r) b ((a + b) + Work.Pi6.vr r) h1
            ((mssD 𝕜 W r a (a + Work.Pi6.vr r)).hom x) y
        + ((-1 : 𝕜) ^ (a.1 + a.2).natAbs) •
          mssMul 𝕜 W r a (b + Work.Pi6.vr r) ((a + b) + Work.Pi6.vr r) h2 x
            ((mssD 𝕜 W r b (b + Work.Pi6.vr r)).hom y) := by
  have hab : Enn (a + b) := Enn_add ha hb
  have hC : Enn ((a + b) + Work.Pi6.vr r) := by
    obtain ⟨ha1, -⟩ := ha
    obtain ⟨hb1, -⟩ := hb
    obtain ⟨-, hA2⟩ := hA
    obtain ⟨-, hB2⟩ := hB
    rw [snd_add_vr] at hA2 hB2
    refine ⟨?_, ?_⟩
    · show 0 ≤ ((a + b) + Work.Pi6.vr r).1
      rw [fst_add_vr]; simp only [Prod.fst_add]
      linarith [Int.natCast_nonneg r]
    · show 0 ≤ ((a + b) + Work.Pi6.vr r).2
      rw [snd_add_vr, Prod.snd_add]
      have hr1 : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast (by omega : 1 ≤ r)
      linarith
  have hsign : ((-1 : 𝕜) ^ (a.1 + a.2).natAbs) = (-1 : 𝕜) ^ EN a := by
    have hna : (a.1 + a.2).natAbs = (a.1 + a.2).toNat := by
      have h2' := Int.toNat_of_nonneg (show (0 : ℤ) ≤ a.1 + a.2 by linarith [ha.1, ha.2])
      have h1' := Int.natAbs_of_nonneg (show (0 : ℤ) ≤ a.1 + a.2 by linarith [ha.1, ha.2])
      exact_mod_cast (h1'.trans h2'.symm)
    rw [hna, EN_of_nonneg ha]
  rw [hsign]
  have e1 : EI a + r + EI b = EI a + EI b + r := by omega
  have e1' : EN a + 1 + EN b = EN a + EN b + 1 := by omega
  have e2 : EI a + (EI b + r) = EI a + EI b + r := by omega
  have e2' : EN a + (EN b + 1) = EN a + EN b + 1 := by omega
  rw [mssMul_self_apply hh x y, mssMulRaw_apply_enn ha hb x y, mssD_apply_enn hab hC,
    pD_pEcast_apply (EI_add ha hb) (EN_add ha hb),
    pd_mul_leib r (EI a) (EN a) (EI b) (EN b) e1 e1' e2 e2' x y,
    mssMul_apply_enn hA hb h1 ((mssD 𝕜 W r a (a + Work.Pi6.vr r)).hom x) y,
    mssD_apply_enn ha hA, pd_mul_pEcast_left,
    mssMul_apply_enn ha hB h2 x ((mssD 𝕜 W r b (b + Work.Pi6.vr r)).hom y),
    mssD_apply_enn hb hB, pd_mul_pEcast_right]
  simp only [pEcast_hom_add, pEcast_hom_smul, pEcast_hom_apply_comp]

/-! ## 3. The degenerate cases, and the Leibniz rule for `a + b` -/

theorem mssMulLeib_ab (r : ℕ) (hr : 2 ≤ r)
    (a b : ℤ × ℤ) (hh : a + b = a + b)
    (h1 : (a + Work.Pi6.vr r) + b = (a + b) + Work.Pi6.vr r)
    (h2 : a + (b + Work.Pi6.vr r) = (a + b) + Work.Pi6.vr r)
    (x : mssE 𝕜 W r a) (y : mssE 𝕜 W r b) :
    (mssD 𝕜 W r (a + b) ((a + b) + Work.Pi6.vr r)).hom
        (mssMul 𝕜 W r a b (a + b) hh x y)
      = mssMul 𝕜 W r (a + Work.Pi6.vr r) b ((a + b) + Work.Pi6.vr r) h1
            ((mssD 𝕜 W r a (a + Work.Pi6.vr r)).hom x) y
        + ((-1 : 𝕜) ^ (a.1 + a.2).natAbs) •
          mssMul 𝕜 W r a (b + Work.Pi6.vr r) ((a + b) + Work.Pi6.vr r) h2 x
            ((mssD 𝕜 W r b (b + Work.Pi6.vr r)).hom y) := by
  by_cases ha : Enn a
  · have hsign : ((-1 : 𝕜) ^ (a.1 + a.2).natAbs) = (-1 : 𝕜) ^ EN a := by
      have hna : (a.1 + a.2).natAbs = (a.1 + a.2).toNat := by
        have h2' := Int.toNat_of_nonneg (show (0 : ℤ) ≤ a.1 + a.2 by linarith [ha.1, ha.2])
        have h1' := Int.natAbs_of_nonneg (show (0 : ℤ) ≤ a.1 + a.2 by linarith [ha.1, ha.2])
        exact_mod_cast (h1'.trans h2'.symm)
      rw [hna, EN_of_nonneg ha]
    rw [hsign]
    by_cases hb : Enn b
    · have hab : Enn (a + b) := Enn_add ha hb
      have e1 : EI a + r + EI b = EI a + EI b + r := by omega
      have e1' : EN a + 1 + EN b = EN a + EN b + 1 := by omega
      have e2 : EI a + (EI b + r) = EI a + EI b + r := by omega
      have e2' : EN a + (EN b + 1) = EN a + EN b + 1 := by omega
      by_cases hA : Enn (a + Work.Pi6.vr r)
      · by_cases hB : Enn (b + Work.Pi6.vr r)
        · rw [← hsign]
          exact mssMulLeib_enn r hr a b ha hb hA hB hh h1 h2 x y
        · -- `hA`, `¬ hB`
          by_cases hC : Enn ((a + b) + Work.Pi6.vr r)
          · have hdy : (mssD 𝕜 W r b (b + Work.Pi6.vr r)).hom y = 0 :=
              mssD_apply_neg hb hB y
            have hV0 : (pD 𝕜 W r (EI b) (EN b)).hom y = 0 := by
              haveI : Subsingleton (pEraw 𝕜 W r (EI b + r) (EN b + 1)) :=
                subsingleton_pEraw_of 𝕜 W r (EI b + r) (EN b + 1) (le_vr r hr hb hB)
              exact Subsingleton.elim _ _
            rw [mssMul_self_apply hh x y, mssMulRaw_apply_enn ha hb x y, mssD_apply_enn hab hC,
              pD_pEcast_apply (EI_add ha hb) (EN_add ha hb),
              pd_mul_leib r (EI a) (EN a) (EI b) (EN b) e1 e1' e2 e2' x y,
              mssMul_apply_enn hA hb h1 ((mssD 𝕜 W r a (a + Work.Pi6.vr r)).hom x) y,
              mssD_apply_enn ha hA, pd_mul_pEcast_left,
              hdy, mssMul_apply_zero_right, hV0]
            simp only [pEcast_hom_add, pEcast_hom_smul, pEcast_hom_apply_comp, map_zero,
              LinearMap.zero_apply, smul_zero, add_zero]
          · -- `¬ hC`
            have hL : (mssD 𝕜 W r (a + b) ((a + b) + Work.Pi6.vr r)).hom
                (mssMul 𝕜 W r a b (a + b) hh x y) = 0 := by
              rw [mssD_self, mssDMain_pos_neg 𝕜 W r hab hC, ModuleCat.hom_zero,
                LinearMap.zero_apply]
            rw [hL]
            haveI : Subsingleton (mssE 𝕜 W r ((a + b) + Work.Pi6.vr r)) :=
              subsingleton_mssE 𝕜 W r hC
            exact Subsingleton.elim _ _
      · -- `¬ hA`
        by_cases hC : Enn ((a + b) + Work.Pi6.vr r)
        · have hdx : (mssD 𝕜 W r a (a + Work.Pi6.vr r)).hom x = 0 :=
            mssD_apply_neg ha hA x
          have hU0 : (pD 𝕜 W r (EI a) (EN a)).hom x = 0 := by
            haveI : Subsingleton (pEraw 𝕜 W r (EI a + r) (EN a + 1)) :=
              subsingleton_pEraw_of 𝕜 W r (EI a + r) (EN a + 1) (le_vr r hr ha hA)
            exact Subsingleton.elim _ _
          by_cases hB : Enn (b + Work.Pi6.vr r)
          · rw [mssMul_self_apply hh x y, mssMulRaw_apply_enn ha hb x y, mssD_apply_enn hab hC,
              pD_pEcast_apply (EI_add ha hb) (EN_add ha hb),
              pd_mul_leib r (EI a) (EN a) (EI b) (EN b) e1 e1' e2 e2' x y,
              hdx, mssMul_apply_zero_left, hU0,
              mssMul_apply_enn ha hB h2 x ((mssD 𝕜 W r b (b + Work.Pi6.vr r)).hom y),
              mssD_apply_enn hb hB, pd_mul_pEcast_right]
            simp only [pEcast_hom_add, pEcast_hom_smul, pEcast_hom_apply_comp, map_zero,
              LinearMap.zero_apply, smul_zero, add_zero, zero_add]
          · have hdy : (mssD 𝕜 W r b (b + Work.Pi6.vr r)).hom y = 0 :=
              mssD_apply_neg hb hB y
            have hV0 : (pD 𝕜 W r (EI b) (EN b)).hom y = 0 := by
              haveI : Subsingleton (pEraw 𝕜 W r (EI b + r) (EN b + 1)) :=
                subsingleton_pEraw_of 𝕜 W r (EI b + r) (EN b + 1) (le_vr r hr hb hB)
              exact Subsingleton.elim _ _
            rw [mssMul_self_apply hh x y, mssMulRaw_apply_enn ha hb x y, mssD_apply_enn hab hC,
              pD_pEcast_apply (EI_add ha hb) (EN_add ha hb),
              pd_mul_leib r (EI a) (EN a) (EI b) (EN b) e1 e1' e2 e2' x y,
              hdx, mssMul_apply_zero_left, hdy, mssMul_apply_zero_right, hU0, hV0]
            simp only [map_zero, LinearMap.zero_apply, smul_zero, add_zero]
        · have hL : (mssD 𝕜 W r (a + b) ((a + b) + Work.Pi6.vr r)).hom
              (mssMul 𝕜 W r a b (a + b) hh x y) = 0 := by
            rw [mssD_self, mssDMain_pos_neg 𝕜 W r hab hC, ModuleCat.hom_zero,
              LinearMap.zero_apply]
          rw [hL]
          haveI : Subsingleton (mssE 𝕜 W r ((a + b) + Work.Pi6.vr r)) :=
            subsingleton_mssE 𝕜 W r hC
          exact Subsingleton.elim _ _
    · -- `¬ hb`
      have hL : (mssD 𝕜 W r (a + b) ((a + b) + Work.Pi6.vr r)).hom
          (mssMul 𝕜 W r a b (a + b) hh x y) = 0 := by
        rw [mssMul_self_apply hh x y, mssMulRaw_apply_neg' ha hb x y]
        simp
      rw [hL, mssMul_eq_zero_right h1 hb]
      have hdy : (mssD 𝕜 W r b (b + Work.Pi6.vr r)).hom y = 0 := by
        rw [mssD_self, mssDMain_neg 𝕜 W r hb, ModuleCat.hom_zero, LinearMap.zero_apply]
      rw [hdy]
      simp [mssMul_apply_zero_right]
  · -- `¬ ha`
    have hL : (mssD 𝕜 W r (a + b) ((a + b) + Work.Pi6.vr r)).hom
        (mssMul 𝕜 W r a b (a + b) hh x y) = 0 := by
      rw [mssMul_self_apply hh x y, mssMulRaw_apply_neg (𝕜 := 𝕜) (W := W) (r := r) ha x y]
      simp
    rw [hL, mssMul_eq_zero_left h2 ha]
    have hdx : (mssD 𝕜 W r a (a + Work.Pi6.vr r)).hom x = 0 := by
      rw [mssD_self, mssDMain_neg 𝕜 W r ha, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [hdx]
    simp [mssMul_apply_zero_left]

end

/-- **The Leibniz rule** for the product and the differential on the pages of the multiplicative
cohomological Serre spectral sequence. -/
theorem mssMulLeib (𝕜 : Type) [Field 𝕜] (W : Work.Pi6.MSS.CohFilt 𝕜) (r : ℕ) (hr : 2 ≤ r)
    (a b c : ℤ × ℤ) (h : a + b = c) (x : Work.Pi6.MSS.mssE 𝕜 W r a)
    (y : Work.Pi6.MSS.mssE 𝕜 W r b) :
    (Work.Pi6.MSS.mssD 𝕜 W r c (c + Work.Pi6.vr r)).hom
        (Work.Pi6.MSS.mssMul 𝕜 W r a b c h x y)
      = Work.Pi6.MSS.mssMul 𝕜 W r (a + Work.Pi6.vr r) b (c + Work.Pi6.vr r)
            (by rw [← h]; abel) ((Work.Pi6.MSS.mssD 𝕜 W r a (a + Work.Pi6.vr r)).hom x) y
        + ((-1 : 𝕜) ^ (a.1 + a.2).natAbs) •
          Work.Pi6.MSS.mssMul 𝕜 W r a (b + Work.Pi6.vr r) (c + Work.Pi6.vr r)
            (by rw [← h]; abel) x ((Work.Pi6.MSS.mssD 𝕜 W r b (b + Work.Pi6.vr r)).hom y) := by
  subst c
  exact mssMulLeib_ab r hr a b _ _ _ x y

end Work.Pi6.MSS
