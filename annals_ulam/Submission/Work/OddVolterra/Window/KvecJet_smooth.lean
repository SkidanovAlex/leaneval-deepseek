import Mathlib
import Submission.Work.OddVolterra.Window.KvecDefs

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-!
# Smoothness of the two component functions `KF1`, `KF2` of the odd Abel kernel jet

The two components of `Kvec n h a σ z` are, off the diagonal and where the Abel radicands are
positive, the compositions of explicit functions of the finite jet with the jet curve
`u ↦ KJet n h σ z u`.  This file proves that the *first* half of that statement is smooth: the
two component functions `KF1 n`, `KF2 n` of the jet variable `v : KJIx n → ℝ` are `C^∞` on the
open set `KJopen n = {v | 0 < v.kd1 ∧ 0 < v.kd2}`, i.e. wherever the two radicands are
non-zero.  (For `v.kd1 = 0` (resp. `v.kd2 = 0`) the factor `Real.sqrt (v.kd1)` (resp. the
`rpow kd ^ (n - 1/2 - i)`) is not differentiable, which is exactly why `KJopen` is the
natural domain.)

The mathematical content is that every factor is either

* a polynomial in the jet coordinates -- the Faà-di-Bruno polynomial `faaDiBrunoJ m α s v`,
  which in fact does not depend on its third argument `s`;
* a projection `v ↦ v i`, hence smooth everywhere;
* `Real.sqrt (v.kd1)`, smooth on `0 < v.kd1`;
* a real power `v.kd1 ^ p`, smooth on `0 < v.kd1` (`Real.contDiffAt_rpow_const_of_ne`).

The technical point is that the Faà-di-Bruno polynomial is written with the (unused) argument
`s = v.aa`, so each smoothness statement about it is first proved for the witness `s = 0`
(where the composition `ContDiff.comp` goes through without unfolding the polynomial) and then
transported by the definitional equality `faaDiBrunoJ m α s v = faaDiBrunoJ m α 0 v`.
-/

noncomputable section

/-! ## Smoothness of the `ℕ`-indexed extractions of the jet blocks -/

/-- The `k`-th derivative block of the perturbation is a smooth function of the jet. -/
lemma KvecJet_contDiff_KJW (n : ℕ) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ => KJW n v k) := by
  by_cases h : k < n + 1
  · simp only [KJW, dif_pos h]
    exact contDiff_apply ℝ ℝ _
  · simp only [KJW, dif_neg h]
    exact contDiff_const

/-- The first radicand jet block, as a `Fin m`-indexed family, is a smooth function of the jet
(as soon as `m ≤ n + 2`). -/
lemma KvecJet_contDiff_KJZ1_pi (n m : ℕ) (hm : m ≤ n + 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ => fun j : Fin m => KJZ1 n v j.1) := by
  rw [contDiff_pi]
  intro j
  have hfun : (fun v : KJIx n → ℝ => (fun j : Fin m => KJZ1 n v j.1) j)
      = fun v : KJIx n → ℝ => v (.Z1 (⟨j.1, lt_of_lt_of_le j.2 hm⟩ : Fin (n + 2))) := by
    funext v
    exact KJZ1_eq n v ⟨j.1, lt_of_lt_of_le j.2 hm⟩
  rw [hfun]
  exact contDiff_apply ℝ ℝ _

/-- The second radicand jet block, as a `Fin m`-indexed family, is a smooth function of the jet
(as soon as `m ≤ n + 2`). -/
lemma KvecJet_contDiff_KJZ2_pi (n m : ℕ) (hm : m ≤ n + 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ => fun j : Fin m => KJZ2 n v j.1) := by
  rw [contDiff_pi]
  intro j
  have hfun : (fun v : KJIx n → ℝ => (fun j : Fin m => KJZ2 n v j.1) j)
      = fun v : KJIx n → ℝ => v (.Z2 (⟨j.1, lt_of_lt_of_le j.2 hm⟩ : Fin (n + 2))) := by
    funext v
    exact KJZ2_eq n v ⟨j.1, lt_of_lt_of_le j.2 hm⟩
  rw [hfun]
  exact contDiff_apply ℝ ℝ _

/-! ## The Faà-di-Bruno factor -/

/-- The Faà-di-Bruno polynomial composed with the first radicand jet block (with the unused
`u`-argument set to `0`) is a smooth function of the jet. -/
lemma KvecJet_contDiff_faaZ1_zero (n m : ℕ) (hm : m ≤ n + 1) (α : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ =>
      Commons.Geometry.Ulam.faaDiBrunoJ m α 0 (fun j : Fin (m + 1) => KJZ1 n v j.1)) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun w : Fin (m + 1) → ℝ =>
      Commons.Geometry.Ulam.faaDiBrunoJ m α 0 w) :=
    Work.OddVolterra.faaDiBrunoJ_contDiff_poly m α 0
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ =>
      (fun j : Fin (m + 1) => KJZ1 n v j.1)) := KvecJet_contDiff_KJZ1_pi n (m + 1) (by omega)
  have hh : ContDiff ℝ (⊤ : ℕ∞) ((fun w : Fin (m + 1) → ℝ =>
      Commons.Geometry.Ulam.faaDiBrunoJ m α 0 w) ∘ (fun v : KJIx n → ℝ =>
      (fun j : Fin (m + 1) => KJZ1 n v j.1))) := hg.comp hf
  exact hh

/-- The Faà-di-Bruno polynomial composed with the second radicand jet block (with the unused
`u`-argument set to `0`) is a smooth function of the jet. -/
lemma KvecJet_contDiff_faaZ2_zero (n m : ℕ) (hm : m ≤ n + 1) (α : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ =>
      Commons.Geometry.Ulam.faaDiBrunoJ m α 0 (fun j : Fin (m + 1) => KJZ2 n v j.1)) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun w : Fin (m + 1) → ℝ =>
      Commons.Geometry.Ulam.faaDiBrunoJ m α 0 w) :=
    Work.OddVolterra.faaDiBrunoJ_contDiff_poly m α 0
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ =>
      (fun j : Fin (m + 1) => KJZ2 n v j.1)) := KvecJet_contDiff_KJZ2_pi n (m + 1) (by omega)
  have hh : ContDiff ℝ (⊤ : ℕ∞) ((fun w : Fin (m + 1) → ℝ =>
      Commons.Geometry.Ulam.faaDiBrunoJ m α 0 w) ∘ (fun v : KJIx n → ℝ =>
      (fun j : Fin (m + 1) => KJZ2 n v j.1))) := hg.comp hf
  exact hh

/-! ## The first component `KF1` -/

/-- `KJk1 n (v.aa) (KJZ1 n v) (v.kd1)`, the first-kernel factor attached to the endpoint
`t₁ = -v.c2`, is smooth on `KJopen n`. -/
lemma KvecJet_contDiffOn_KJk1_Z1 (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun v : KJIx n → ℝ => KJk1 n (v .aa) (KJZ1 n v) (v .kd1)) (KJopen n) := by
  have hnum : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ =>
      Commons.Geometry.Ulam.faaDiBrunoJ (n + 1) ((n : ℝ) + 1 / 2) 0
        (fun j : Fin (n + 2) => KJZ1 n v j.1)) (KJopen n) :=
    (KvecJet_contDiff_faaZ1_zero n (n + 1) (le_refl _) _).contDiffOn
  have hgoal : (fun v : KJIx n → ℝ => KJk1 n (v .aa) (KJZ1 n v) (v .kd1))
      = fun v : KJIx n → ℝ =>
        Commons.Geometry.Ulam.faaDiBrunoJ (n + 1) ((n : ℝ) + 1 / 2) 0
          (fun j : Fin (n + 2) => KJZ1 n v j.1) / Real.sqrt (v .kd1) := by
    funext v; rfl
  rw [hgoal]
  refine ContDiffOn.div hnum ?_ ?_
  · exact ContDiffOn.sqrt ((contDiff_apply ℝ ℝ KJIx.kd1).contDiffOn)
      (fun v hv => ne_of_gt hv.1)
  · intro v hv
    exact ne_of_gt (Real.sqrt_pos_of_pos hv.1)

/-- `KJk1 n (v.aa) (KJZ2 n v) (v.kd2)`, the first-kernel factor attached to the endpoint
`t₂ = v.c3`, is smooth on `KJopen n`. -/
lemma KvecJet_contDiffOn_KJk1_Z2 (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun v : KJIx n → ℝ => KJk1 n (v .aa) (KJZ2 n v) (v .kd2)) (KJopen n) := by
  have hnum : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ =>
      Commons.Geometry.Ulam.faaDiBrunoJ (n + 1) ((n : ℝ) + 1 / 2) 0
        (fun j : Fin (n + 2) => KJZ2 n v j.1)) (KJopen n) :=
    (KvecJet_contDiff_faaZ2_zero n (n + 1) (le_refl _) _).contDiffOn
  have hgoal : (fun v : KJIx n → ℝ => KJk1 n (v .aa) (KJZ2 n v) (v .kd2))
      = fun v : KJIx n → ℝ =>
        Commons.Geometry.Ulam.faaDiBrunoJ (n + 1) ((n : ℝ) + 1 / 2) 0
          (fun j : Fin (n + 2) => KJZ2 n v j.1) / Real.sqrt (v .kd2) := by
    funext v; rfl
  rw [hgoal]
  refine ContDiffOn.div hnum ?_ ?_
  · exact ContDiffOn.sqrt ((contDiff_apply ℝ ℝ KJIx.kd2).contDiffOn)
      (fun v hv => ne_of_gt hv.2)
  · intro v hv
    exact ne_of_gt (Real.sqrt_pos_of_pos hv.2)

/-- The first component `KF1 n` of the kernel vector is `C^∞` on `KJopen n`. -/
theorem KvecJet_KF1_smooth (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ => KF1 n v) (KJopen n) := by
  have hgoal : (fun v : KJIx n → ℝ => KF1 n v) = fun v : KJIx n → ℝ =>
      -(KJk1 n (v .aa) (KJZ1 n v) (v .kd1) * v .c2 +
        KJk1 n (v .aa) (KJZ2 n v) (v .kd2) * v .c3) := by
    funext v; rfl
  rw [hgoal]
  exact ContDiffOn.neg (ContDiffOn.add
    (ContDiffOn.mul (KvecJet_contDiffOn_KJk1_Z1 n) (contDiff_apply ℝ ℝ KJIx.c2).contDiffOn)
    (ContDiffOn.mul (KvecJet_contDiffOn_KJk1_Z2 n) (contDiff_apply ℝ ℝ KJIx.c3).contDiffOn))

/-! ## The second component `KF2` -/

/-- The tail factor of `KJk2`: for `n - i = 0` it is an endpoint value shifted by the derivative
`W 0`, otherwise it is `W (n - i)`.  Both branches are smooth functions of the jet (the branch is
decided by the `i`-index alone, not by the jet). -/
lemma KvecJet_contDiffOn_KJW_if (n i : ℕ) {e : (KJIx n → ℝ) → ℝ}
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e (KJopen n)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ =>
      (if n - i = 0 then e v + KJW n v 0 else KJW n v (n - i))) (KJopen n) := by
  by_cases h : n - i = 0
  · have hfun : (fun v : KJIx n → ℝ =>
        (if n - i = 0 then e v + KJW n v 0 else KJW n v (n - i)))
        = fun v : KJIx n → ℝ => e v + KJW n v 0 := by
      funext v; exact if_pos h
    rw [hfun]
    exact he.add (KvecJet_contDiff_KJW n 0).contDiffOn
  · have hfun : (fun v : KJIx n → ℝ =>
        (if n - i = 0 then e v + KJW n v 0 else KJW n v (n - i)))
        = fun v : KJIx n → ℝ => KJW n v (n - i) := by
      funext v; exact if_neg h
    rw [hfun]
    exact (KvecJet_contDiff_KJW n (n - i)).contDiffOn

/-- `KJk2 n (v.aa) (v.sg) (v.t1) (KJZ1 n v) (v.kd1) (KJW n v)`, the second-kernel factor
attached to the endpoint `t₁ = -v.c2`, is smooth on `KJopen n`. -/
lemma KvecJet_contDiffOn_KJk2_Z1 (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun v : KJIx n → ℝ => KJk2 n (v .aa) (v .sg) (v .t1) (KJZ1 n v) (v .kd1) (KJW n v))
      (KJopen n) := by
  have hgoal : (fun v : KJIx n → ℝ =>
        KJk2 n (v .aa) (v .sg) (v .t1) (KJZ1 n v) (v .kd1) (KJW n v))
      = fun v : KJIx n → ℝ => ∑ i ∈ Finset.range (n + 1),
          ((n.choose i : ℕ) : ℝ) *
            Commons.Geometry.Ulam.faaDiBrunoJ i ((n : ℝ) - 1 / 2) 0
              (fun j : Fin (i + 1) => KJZ1 n v j.1) *
            (v .sg - v .aa) ^ (n - i) * (v .kd1) ^ (((n : ℝ) - 1 / 2) - (i : ℝ)) *
            (if n - i = 0 then v .t1 + KJW n v 0 else KJW n v (n - i)) := by
    funext v; rfl
  rw [hgoal]
  refine ContDiffOn.sum (fun i hi => ?_)
  simp only [Finset.mem_range] at hi
  have hFB : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ =>
      Commons.Geometry.Ulam.faaDiBrunoJ i ((n : ℝ) - 1 / 2) 0
        (fun j : Fin (i + 1) => KJZ1 n v j.1)) (KJopen n) :=
    (KvecJet_contDiff_faaZ1_zero n i (by omega) ((n : ℝ) - 1 / 2)).contDiffOn
  have hP : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ => (v .sg - v .aa) ^ (n - i))
      (KJopen n) :=
    ContDiffOn.pow (ContDiffOn.sub (contDiff_apply ℝ ℝ KJIx.sg).contDiffOn
      (contDiff_apply ℝ ℝ KJIx.aa).contDiffOn) _
  have hR : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun v : KJIx n → ℝ => (v .kd1) ^ (((n : ℝ) - 1 / 2) - (i : ℝ))) (KJopen n) :=
    Work.OddVolterra.contDiff_rpow_const (isOpen_KJopen n)
      ((contDiff_apply ℝ ℝ KJIx.kd1).contDiffOn) (fun v hv => ne_of_gt hv.1) _
  exact ContDiffOn.mul (ContDiffOn.mul (ContDiffOn.mul
    (ContDiffOn.mul contDiffOn_const hFB) hP) hR)
    (KvecJet_contDiffOn_KJW_if n i (e := fun v : KJIx n → ℝ => v .t1)
      (contDiff_apply ℝ ℝ KJIx.t1).contDiffOn)

/-- `KJk2 n (v.aa) (v.sg) (v.t2) (KJZ2 n v) (v.kd2) (KJW n v)`, the second-kernel factor
attached to the endpoint `t₂ = v.c3`, is smooth on `KJopen n`. -/
lemma KvecJet_contDiffOn_KJk2_Z2 (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun v : KJIx n → ℝ => KJk2 n (v .aa) (v .sg) (v .t2) (KJZ2 n v) (v .kd2) (KJW n v))
      (KJopen n) := by
  have hgoal : (fun v : KJIx n → ℝ =>
        KJk2 n (v .aa) (v .sg) (v .t2) (KJZ2 n v) (v .kd2) (KJW n v))
      = fun v : KJIx n → ℝ => ∑ i ∈ Finset.range (n + 1),
          ((n.choose i : ℕ) : ℝ) *
            Commons.Geometry.Ulam.faaDiBrunoJ i ((n : ℝ) - 1 / 2) 0
              (fun j : Fin (i + 1) => KJZ2 n v j.1) *
            (v .sg - v .aa) ^ (n - i) * (v .kd2) ^ (((n : ℝ) - 1 / 2) - (i : ℝ)) *
            (if n - i = 0 then v .t2 + KJW n v 0 else KJW n v (n - i)) := by
    funext v; rfl
  rw [hgoal]
  refine ContDiffOn.sum (fun i hi => ?_)
  simp only [Finset.mem_range] at hi
  have hFB : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ =>
      Commons.Geometry.Ulam.faaDiBrunoJ i ((n : ℝ) - 1 / 2) 0
        (fun j : Fin (i + 1) => KJZ2 n v j.1)) (KJopen n) :=
    (KvecJet_contDiff_faaZ2_zero n i (by omega) ((n : ℝ) - 1 / 2)).contDiffOn
  have hP : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ => (v .sg - v .aa) ^ (n - i))
      (KJopen n) :=
    ContDiffOn.pow (ContDiffOn.sub (contDiff_apply ℝ ℝ KJIx.sg).contDiffOn
      (contDiff_apply ℝ ℝ KJIx.aa).contDiffOn) _
  have hR : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun v : KJIx n → ℝ => (v .kd2) ^ (((n : ℝ) - 1 / 2) - (i : ℝ))) (KJopen n) :=
    Work.OddVolterra.contDiff_rpow_const (isOpen_KJopen n)
      ((contDiff_apply ℝ ℝ KJIx.kd2).contDiffOn) (fun v hv => ne_of_gt hv.2) _
  exact ContDiffOn.mul (ContDiffOn.mul (ContDiffOn.mul
    (ContDiffOn.mul contDiffOn_const hFB) hP) hR)
    (KvecJet_contDiffOn_KJW_if n i (e := fun v : KJIx n → ℝ => v .t2)
      (contDiff_apply ℝ ℝ KJIx.t2).contDiffOn)

/-- The second component `KF2 n` of the kernel vector is `C^∞` on `KJopen n`. -/
theorem KvecJet_KF2_smooth (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ => KF2 n v) (KJopen n) := by
  have hgoal : (fun v : KJIx n → ℝ => KF2 n v) = fun v : KJIx n → ℝ =>
      -(KJk2 n (v .aa) (v .sg) (v .t1) (KJZ1 n v) (v .kd1) (KJW n v) * v .c2 +
        KJk2 n (v .aa) (v .sg) (v .t2) (KJZ2 n v) (v .kd2) (KJW n v) * v .c3) := by
    funext v; rfl
  rw [hgoal]
  exact ContDiffOn.neg (ContDiffOn.add
    (ContDiffOn.mul (KvecJet_contDiffOn_KJk2_Z1 n) (contDiff_apply ℝ ℝ KJIx.c2).contDiffOn)
    (ContDiffOn.mul (KvecJet_contDiffOn_KJk2_Z2 n) (contDiff_apply ℝ ℝ KJIx.c3).contDiffOn))

/-- **The two component functions of the odd Abel kernel vector are smooth on the region where
both radicands are non-zero.** -/
theorem KvecJet_smooth (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ => KF1 n v) (KJopen n) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ => KF2 n v) (KJopen n) :=
  ⟨KvecJet_KF1_smooth n, KvecJet_KF2_smooth n⟩

end

end Work.OddVolterra.Window
