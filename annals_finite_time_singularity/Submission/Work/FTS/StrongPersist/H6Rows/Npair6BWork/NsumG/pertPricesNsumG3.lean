import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.coefData_pertSharp
import Submission.Work.FTS.StrongPersist.H6Row6.row6PertData

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `pertPricesNsumG3` — the `CoefData` of the three perturbed residual fields, flat prices

The pointwise/sharp version of this statement is `Npair6BWork.coefData_pertSharp` (PROVED):
under exactly the hypotheses used here (`HQo α 4 f`, `Xn α f ≤ M`, `EllPkgGo α Ce f F`,
`EllPkgK α 6 Ce f F`) it prices

* `Rop α (PhiTil α f F)`            by `K α^{-1/2} |Ce| M`, `|Ce| M`, `|Ce| HkNorm α 6 f`,
* `Uop α (PhiTil α f F) / s2`       by the same,
* `Vop (PhiTil α f F)`            by the same.

The three fields appearing here are the scalar multiples `2 ·`, `-2 ·` and `-2α ·` of those,
so the whole `CoefData` transport is the scalar bookkeeping of `H6Row6/row6PertData.lean`
(`r6_coefData_const_mul`, `r6_coefData_mono`) plus three elementary arithmetic lemmas, where
the `α^{-1/2}`-factor is paid for by the flat `(1+|Ce|)(1+M)`-budget and the extra `α ≤ 1`.

The last two conjuncts are the flat angular data of the `V`-slot: `CoefThMem 1` and `CoefTh 1`
are transported through the scalar `-2α` by
`H6Row6.r6_coefThMem_const_mul` / `r6_coefTh_const_mul_le`, and the `α^{-1/2}` in
`EllPkgGo.Vth` (`CoefTh 1 (Vop …) ≤ Ce α^{-1/2} Xn α f`) is *cancelled* by the `α` of the
scalar: `2α · α^{-1/2} = 2α^{1/2} ≤ 2`.  Note that `Ce` has an arbitrary sign here; the
`|Ce|`-form of every price is obtained with `le_abs_self`, never by assuming `0 < Ce`.
-/

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG

open scoped Real
open Work.FTS.StrongPersist.H6Pair6Aux.T6Coef (CoefData)

/-! ## The three arithmetic lemmas

All prices carry a common factor `α^{-1/2}` (only nonnegativity of `α` is used), and the
`K0`/`K4`/`K6`-slots are traded against `(1+|Ce|)(1+M)`, `(1+|Ce|)M` and
`(1+|Ce|) HkNorm α 6 f`.  The parameter `a` is the extra factor of `α` coming from the scalar
`-2α` of the `V`-slot (`a = 1` for the `R`/`U`-slots). -/

/-- The `K0`-arithmetic. -/
private lemma pertPrice0 {α a K Ce M : ℝ} (hα0 : 0 ≤ α) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hK : 0 ≤ K) (hM : 0 ≤ M) :
    2 * a * (K * α ^ (-(1 / 2 : ℝ)) * |Ce| * M)
      ≤ (2 * K + 1) * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M) := by
  have hr : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0 _
  have hCe : 0 ≤ |Ce| := abs_nonneg Ce
  have h1 : |Ce| * M ≤ (1 + |Ce|) * (1 + M) := by
    nlinarith [hCe, hM, mul_nonneg hCe hM]
  have h2 : 2 * a * K ≤ 2 * K + 1 := by nlinarith
  have h3 : 0 ≤ |Ce| * M := mul_nonneg hCe hM
  calc 2 * a * (K * α ^ (-(1 / 2 : ℝ)) * |Ce| * M)
      = (2 * a * K) * (α ^ (-(1 / 2 : ℝ)) * (|Ce| * M)) := by ring
    _ ≤ (2 * K + 1) * (α ^ (-(1 / 2 : ℝ)) * ((1 + |Ce|) * (1 + M))) :=
        mul_le_mul h2 (mul_le_mul_of_nonneg_left h1 hr)
          (mul_nonneg hr h3) (by linarith)
    _ = (2 * K + 1) * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M) := by ring

/-- The `K4`-arithmetic (the `M`-slot). -/
private lemma pertPrice4 {a Ce M : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hM : 0 ≤ M) :
    2 * a * (|Ce| * M) ≤ 2 * (1 + |Ce|) * M := by
  have hCe : 0 ≤ |Ce| := abs_nonneg Ce
  have h1 : |Ce| * M ≤ (1 + |Ce|) * M :=
    mul_le_mul_of_nonneg_right (by linarith) hM
  have h2 : 2 * a ≤ 2 := by linarith
  calc 2 * a * (|Ce| * M) ≤ 2 * (|Ce| * M) :=
        mul_le_mul_of_nonneg_right h2 (mul_nonneg hCe hM)
    _ ≤ 2 * ((1 + |Ce|) * M) := mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = 2 * (1 + |Ce|) * M := by ring

/-- The `K6`-arithmetic (the `HkNorm`-slot). -/
private lemma pertPrice6 {a Ce x : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : 0 ≤ x) :
    2 * a * (|Ce| * x) ≤ 2 * (1 + |Ce|) * x := by
  have hCe : 0 ≤ |Ce| := abs_nonneg Ce
  have h1 : |Ce| * x ≤ (1 + |Ce|) * x :=
    mul_le_mul_of_nonneg_right (by linarith) hx
  have h2 : 2 * a ≤ 2 := by linarith
  calc 2 * a * (|Ce| * x) ≤ 2 * (|Ce| * x) :=
        mul_le_mul_of_nonneg_right h2 (mul_nonneg hCe hx)
    _ ≤ 2 * ((1 + |Ce|) * x) := mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = 2 * (1 + |Ce|) * x := by ring

theorem pertPricesNsumG3 : ∃ C0 C1 : ℝ, 0 < C0 ∧ 0 ≤ C1 ∧
    ∀ α ∈ Set.Ioc 0 1, ∀ (Ce M : ℝ) (f F : Work.FTS.Galerkin.Fn),
      Work.FTS.VocabO.HQo α 4 f → Work.FTS.Nonlin.Xn α f ≤ M →
      Work.FTS.VocabO.EllPkgGo α Ce f F → Work.FTS.StrongPersist.EllPkgK α 6 Ce f F →
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α
          (fun z θ => 2 * Work.Construction.Rop α (Work.Construction.PhiTil α f F) z θ)
          (C0 * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) (2 * (1 + |Ce|) * M)
          (2 * (1 + |Ce|) * Work.Spaces.HkNorm α 6 f) ∧
       Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α
          (fun z θ => -2 * (Work.Construction.Uop α (Work.Construction.PhiTil α f F) z θ
            / Work.Construction.s2 θ))
          (C0 * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) (2 * (1 + |Ce|) * M)
          (2 * (1 + |Ce|) * Work.Spaces.HkNorm α 6 f) ∧
       Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α
          (fun z θ => -2 * α * Work.Construction.Vop (Work.Construction.PhiTil α f F) z θ)
          (C0 * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) (2 * (1 + |Ce|) * M)
          (2 * (1 + |Ce|) * Work.Spaces.HkNorm α 6 f) ∧
       Work.FTS.VocabO.CoefThMem 1
          (fun z θ => -2 * α * Work.Construction.Vop (Work.Construction.PhiTil α f F) z θ) ∧
       Work.FTS.VocabO.CoefTh 1
          (fun z θ => -2 * α * Work.Construction.Vop (Work.Construction.PhiTil α f F) z θ)
          ≤ C1 * (1 + |Ce|) * (1 + M)) := by
  obtain ⟨K, hKpos, hsharp⟩ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.coefData_pertSharp
  refine ⟨2 * K + 1, 2, by linarith, by norm_num, ?_⟩
  intro α hαI Ce M f F hHQ hXM hGo hK
  have hα0 : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hXM
  have hK0 : 0 ≤ K := hKpos.le
  have hCe0 : 0 ≤ |Ce| := abs_nonneg Ce
  have hr : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0.le _
  -- the sharp data of the three fields, from `coefData_pertSharp`
  obtain ⟨hRd, hUd, hVd⟩ := hsharp α hαI Ce M f F hHQ hXM hGo hK
  -- nonnegativity of the three sharp prices
  have hK0nn : 0 ≤ K * α ^ (-(1 / 2 : ℝ)) * |Ce| * M :=
    mul_nonneg (mul_nonneg (mul_nonneg hK0 hr) hCe0) hMnn
  have hK4nn : 0 ≤ |Ce| * M := mul_nonneg hCe0 hMnn
  have hK6nn : 0 ≤ |Ce| * Work.Spaces.HkNorm α 6 f :=
    mul_nonneg hCe0 (Work.Spaces.HkNorm_nonneg α 6 f)
  have h2abs : |(2 : ℝ)| = 2 := by norm_num
  have hm2abs : |(-2 : ℝ)| = 2 := by norm_num
  have hma : |(-2 : ℝ) * α| = 2 * α := by
    rw [abs_mul, abs_of_pos hα0]
    norm_num
  -- the three target prices for the `R`-slot
  have h0R : |(2 : ℝ)| * (K * α ^ (-(1 / 2 : ℝ)) * |Ce| * M)
      ≤ (2 * K + 1) * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M) := by
    rw [h2abs]
    simpa using pertPrice0 hα0.le (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 1)
      hK0 hMnn
  have h4R : |(2 : ℝ)| * (|Ce| * M) ≤ 2 * (1 + |Ce|) * M := by
    rw [h2abs]
    simpa using pertPrice4 (a := (1 : ℝ)) (by norm_num) (by norm_num) hMnn
  have h6R : |(2 : ℝ)| * (|Ce| * Work.Spaces.HkNorm α 6 f)
      ≤ 2 * (1 + |Ce|) * Work.Spaces.HkNorm α 6 f := by
    rw [h2abs]
    simpa using pertPrice6 (a := (1 : ℝ)) (by norm_num) (by norm_num)
      (Work.Spaces.HkNorm_nonneg α 6 f)
  -- the `R`-slot
  have hRraw : CoefData α
      (fun z θ => 2 * Work.Construction.Rop α (Work.Construction.PhiTil α f F) z θ)
      (|(2 : ℝ)| * (K * α ^ (-(1 / 2 : ℝ)) * |Ce| * M))
      (|(2 : ℝ)| * (|Ce| * M)) (|(2 : ℝ)| * (|Ce| * Work.Spaces.HkNorm α 6 f)) :=
    Work.FTS.StrongPersist.H6Row6.r6_coefData_const_mul (α := α) (c := 2)
      (A := Work.Construction.Rop α (Work.Construction.PhiTil α f F))
      hRd.sm hRd.h4 hRd.h6 hRd.val hRd.n4 hRd.n6 hK0nn hK4nn hK6nn
  have hRdata : CoefData α
      (fun z θ => 2 * Work.Construction.Rop α (Work.Construction.PhiTil α f F) z θ)
      ((2 * K + 1) * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
      (2 * (1 + |Ce|) * M) (2 * (1 + |Ce|) * Work.Spaces.HkNorm α 6 f) :=
    Work.FTS.StrongPersist.H6Row6.r6_coefData_mono hRraw h0R h4R h6R
  -- the `U`-slot
  have h0U : |(-2 : ℝ)| * (K * α ^ (-(1 / 2 : ℝ)) * |Ce| * M)
      ≤ (2 * K + 1) * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M) := by
    rw [hm2abs]
    simpa using pertPrice0 hα0.le (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 1)
      hK0 hMnn
  have h4U : |(-2 : ℝ)| * (|Ce| * M) ≤ 2 * (1 + |Ce|) * M := by
    rw [hm2abs]
    simpa using pertPrice4 (a := (1 : ℝ)) (by norm_num) (by norm_num) hMnn
  have h6U : |(-2 : ℝ)| * (|Ce| * Work.Spaces.HkNorm α 6 f)
      ≤ 2 * (1 + |Ce|) * Work.Spaces.HkNorm α 6 f := by
    rw [hm2abs]
    simpa using pertPrice6 (a := (1 : ℝ)) (by norm_num) (by norm_num)
      (Work.Spaces.HkNorm_nonneg α 6 f)
  have hUraw : CoefData α
      (fun z θ => -2 * (Work.Construction.Uop α (Work.Construction.PhiTil α f F) z θ
        / Work.Construction.s2 θ))
      (|(-2 : ℝ)| * (K * α ^ (-(1 / 2 : ℝ)) * |Ce| * M))
      (|(-2 : ℝ)| * (|Ce| * M)) (|(-2 : ℝ)| * (|Ce| * Work.Spaces.HkNorm α 6 f)) :=
    Work.FTS.StrongPersist.H6Row6.r6_coefData_const_mul (α := α) (c := -2)
      (A := fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f F) z θ
        / Work.Construction.s2 θ)
      hUd.sm hUd.h4 hUd.h6 hUd.val hUd.n4 hUd.n6 hK0nn hK4nn hK6nn
  have hUdata : CoefData α
      (fun z θ => -2 * (Work.Construction.Uop α (Work.Construction.PhiTil α f F) z θ
        / Work.Construction.s2 θ))
      ((2 * K + 1) * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
      (2 * (1 + |Ce|) * M) (2 * (1 + |Ce|) * Work.Spaces.HkNorm α 6 f) :=
    Work.FTS.StrongPersist.H6Row6.r6_coefData_mono hUraw h0U h4U h6U
  -- the `V`-slot
  have h0V : |(-2 : ℝ) * α| * (K * α ^ (-(1 / 2 : ℝ)) * |Ce| * M)
      ≤ (2 * K + 1) * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M) := by
    rw [hma]
    exact pertPrice0 hα0.le hα0.le hα1 hK0 hMnn
  have h4V : |(-2 : ℝ) * α| * (|Ce| * M) ≤ 2 * (1 + |Ce|) * M := by
    rw [hma]
    exact pertPrice4 hα0.le hα1 hMnn
  have h6V : |(-2 : ℝ) * α| * (|Ce| * Work.Spaces.HkNorm α 6 f)
      ≤ 2 * (1 + |Ce|) * Work.Spaces.HkNorm α 6 f := by
    rw [hma]
    exact pertPrice6 hα0.le hα1 (Work.Spaces.HkNorm_nonneg α 6 f)
  have hVraw : CoefData α
      (fun z θ => -2 * α * Work.Construction.Vop (Work.Construction.PhiTil α f F) z θ)
      (|(-2 : ℝ) * α| * (K * α ^ (-(1 / 2 : ℝ)) * |Ce| * M))
      (|(-2 : ℝ) * α| * (|Ce| * M))
      (|(-2 : ℝ) * α| * (|Ce| * Work.Spaces.HkNorm α 6 f)) :=
    Work.FTS.StrongPersist.H6Row6.r6_coefData_const_mul (α := α) (c := -2 * α)
      (A := Work.Construction.Vop (Work.Construction.PhiTil α f F))
      hVd.sm hVd.h4 hVd.h6 hVd.val hVd.n4 hVd.n6 hK0nn hK4nn hK6nn
  have hVdata : CoefData α
      (fun z θ => -2 * α * Work.Construction.Vop (Work.Construction.PhiTil α f F) z θ)
      ((2 * K + 1) * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
      (2 * (1 + |Ce|) * M) (2 * (1 + |Ce|) * Work.Spaces.HkNorm α 6 f) :=
    Work.FTS.StrongPersist.H6Row6.r6_coefData_mono hVraw h0V h4V h6V
  -- the flat angular data of the `V`-slot
  have hVmem : Work.FTS.VocabO.CoefThMem 1
      (fun z θ => -2 * α * Work.Construction.Vop (Work.Construction.PhiTil α f F) z θ) :=
    Work.FTS.StrongPersist.H6Row6.r6_coefThMem_const_mul (l := 1) (c := -2 * α)
      (g := Work.Construction.Vop (Work.Construction.PhiTil α f F)) hGo.Vth.1
  have hVth : Work.FTS.VocabO.CoefTh 1
      (fun z θ => -2 * α * Work.Construction.Vop (Work.Construction.PhiTil α f F) z θ)
      ≤ 2 * (1 + |Ce|) * (1 + M) := by
    have h1 := Work.FTS.StrongPersist.H6Row6.r6_coefTh_const_mul_le (l := 1) (c := -2 * α)
      (g := Work.Construction.Vop (Work.Construction.PhiTil α f F)) hGo.Vth.1
    rw [hma] at h1
    -- the `α^{-1/2}`-priced `CoefTh` bound, upgraded to the `|Ce|`-form (no sign hypothesis)
    have hXnn : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
    have hcoef : Work.FTS.VocabO.CoefTh 1
        (Work.Construction.Vop (Work.Construction.PhiTil α f F))
        ≤ |Ce| * α ^ (-(1 / 2 : ℝ)) * M := by
      have ha : Ce * α ^ (-(1 / 2 : ℝ)) ≤ |Ce| * α ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_abs_self Ce) hr
      have hb : Ce * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f
          ≤ |Ce| * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f :=
        mul_le_mul_of_nonneg_right ha hXnn
      have hc : |Ce| * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f
          ≤ |Ce| * α ^ (-(1 / 2 : ℝ)) * M :=
        mul_le_mul_of_nonneg_left hXM (mul_nonneg hCe0 hr)
      exact le_trans hGo.Vth.2 (le_trans hb hc)
    have h4 : 2 * α * Work.FTS.VocabO.CoefTh 1
        (Work.Construction.Vop (Work.Construction.PhiTil α f F))
        ≤ 2 * α * (|Ce| * α ^ (-(1 / 2 : ℝ)) * M) :=
      mul_le_mul_of_nonneg_left hcoef (by linarith)
    -- the `α · α^{-1/2} = α^{1/2} ≤ 1` cancellation
    have har : α * α ^ (-(1 / 2 : ℝ)) = α ^ (1 / 2 : ℝ) := by
      have h1 : α ^ (1 / 2 : ℝ) = α ^ (1 : ℝ) * α ^ (-(1 / 2 : ℝ)) := by
        have h := Real.rpow_add hα0 (1 : ℝ) (-(1 / 2 : ℝ))
        rw [show (1 : ℝ) + -(1 / 2) = 1 / 2 by norm_num] at h
        exact h
      rw [h1, Real.rpow_one]
    have har1 : α ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hα0.le hα1 (by norm_num)
    have hCeM : |Ce| * M ≤ (1 + |Ce|) * (1 + M) := by
      nlinarith [hCe0, hMnn, mul_nonneg hCe0 hMnn]
    have hpos : 0 ≤ (1 + |Ce|) * (1 + M) := by nlinarith [hCe0, hMnn, mul_nonneg hCe0 hMnn]
    have h5 : 2 * α * (|Ce| * α ^ (-(1 / 2 : ℝ)) * M) ≤ 2 * (1 + |Ce|) * (1 + M) := by
      have hb : α ^ (1 / 2 : ℝ) * (|Ce| * M) ≤ 1 * ((1 + |Ce|) * (1 + M)) :=
        calc α ^ (1 / 2 : ℝ) * (|Ce| * M)
            ≤ α ^ (1 / 2 : ℝ) * ((1 + |Ce|) * (1 + M)) :=
              mul_le_mul_of_nonneg_left hCeM (Real.rpow_nonneg hα0.le _)
          _ ≤ 1 * ((1 + |Ce|) * (1 + M)) := mul_le_mul_of_nonneg_right har1 hpos
      calc 2 * α * (|Ce| * α ^ (-(1 / 2 : ℝ)) * M)
          = 2 * (α * α ^ (-(1 / 2 : ℝ)) * (|Ce| * M)) := by ring
        _ = 2 * (α ^ (1 / 2 : ℝ) * (|Ce| * M)) := by rw [har]
        _ ≤ 2 * (1 * ((1 + |Ce|) * (1 + M))) := mul_le_mul_of_nonneg_left hb (by norm_num)
        _ = 2 * (1 + |Ce|) * (1 + M) := by ring
    exact le_trans (le_trans h1 h4) h5
  exact ⟨hRdata, hUdata, hVdata, hVmem, hVth⟩

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG
