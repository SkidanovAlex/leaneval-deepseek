import Mathlib
import Submission.Work.Diff.Alg.Pinch.Ccone_transversal_a_aux
import Submission.Work.Diff.Alg.Pinch.inPIC2_cone_basic
import Submission.Work.Diff.Alg.Pinch.inPIC2_metric_basic
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.Linv
import Submission.Work.Diff.Alg.Pinch.ell_inv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Monotonicity of the second branch of the Brendle–Schoen family

For `1/2 ≤ s` the Brendle–Schoen pinching cone is

`Ĉ(s) = Ccone s (1/2) (1 - 4/((n-2) + 8s))`,

i.e. the Böhm–Wilking cone `ℓ_{s,1/2}(Dpic p)` with the *fixed* parameter `b = 1/2`.  Unlike the
first branch `0 < s ≤ 1/2` (where `b = s` varies and monotonicity is **false**, see
`Work.Diff.Alg.Pinch.Chat_mono_counterexample`), here the family is decreasing in `s`: the two
cones differ by the translation `R ↦ R + t • Iso n`.

Concretely, given `1/2 ≤ s ≤ s'` put `p = 1 - 4/((n-2)+8s)`, `p' = 1 - 4/((n-2)+8s')` (so that
`p ≤ p' ≤ 1`) and, for `R ∈ Dpic p'`,

`t := 2 (s' - s) scalAlg R / (n (1 + 2 s (n - 1))) ≥ 0`.

Then

* `R + t • Iso n ∈ Dpic p`: `IsAlgCurv` is a linear notion, `InPIC2` is a convex cone containing
  `Iso n` (`inPIC2_cone_basic`), so it is preserved by adding `t • Iso n` with `t ≥ 0`; and
  `ric0 (R + t • Iso n) = ric0 R`, `scalAlg (R + t • Iso n) = scalAlg R + t n (n-1)`, so with
  `scalAlg R ≥ 0` (`inPIC2_metric_basic`), `p ≤ p'` and `p ≤ 1` the Ricci pinching `p` follows
  from the one at `p'`.
* `ℓ_{s,1/2} (R + t • Iso n) = ℓ_{s',1/2} R`.  Indeed
  `ℓ_{a,1/2} R = (R + (1/2)·Ric₀(R) ∧ id) + (2a scalAlg R / n)·Iso n` and
  `ℓ_{a,1/2}(Iso n) = (1 + 2a(n-1))·Iso n`, so the identity is equivalent to
  `2 s scalAlg R / n + t (1 + 2s(n-1)) = 2 s' scalAlg R / n`, which is exactly the definition of
  `t`.

Hence `Ĉ(s') ⊆ Ĉ(s)` for `1/2 ≤ s ≤ s'`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- The Böhm–Wilking transform `ℓ_{a,1/2}`, split off its `Iso`-component:
`ℓ_{a,1/2} R = (R + (1/2)·Ric₀(R) ∧ id) + (2a scalAlg R / n)·Iso n`. -/
private lemma ell_half_eq (a : ℝ) (R : Curv4 n) :
    ell a (1 / 2) R
      = (R + (1 / 2 : ℝ) • knProd (ric0 R) (id2 n)) + (2 * a * scalAlg R / (n : ℝ)) • Iso n := by
  rw [ell, knProd_id2_id2, smul_smul]
  congr 1
  rw [show (a / (n : ℝ) * scalAlg R) * 2 = 2 * a * scalAlg R / (n : ℝ) by ring]

/-- Shifting by `t • Iso n` inside `ℓ_{a,1/2}`:
`ℓ_{a,1/2}(R + t • Iso n) = ℓ_{a,1/2} R + (t (1 + 2a(n-1))) • Iso n`. -/
private lemma ell_half_add_smul_iso (a t : ℝ) (R : Curv4 n) :
    ell a (1 / 2) (R + t • Iso n)
      = ell a (1 / 2) R + (t * (1 + 2 * a * ((n : ℝ) - 1))) • Iso n := by
  rw [ell_add, ell_smul, ell_iso, smul_smul]

private lemma ric_smul_iso (t : ℝ) (i j : Fin n) :
    ric (t • Iso n) i j = t * ((n : ℝ) - 1) * id2 n i j := by
  rw [ric_smul_linv, ric_iso]; ring

private lemma scalAlg_smul_iso (t : ℝ) :
    scalAlg (t • Iso n) = t * ((n : ℝ) * ((n : ℝ) - 1)) := by
  rw [scalAlg_smul_linv, scalAlg_iso]

private lemma ric_add_smul_iso (t : ℝ) (R : Curv4 n) (i j : Fin n) :
    ric (R + t • Iso n) i j = ric R i j + t * ((n : ℝ) - 1) * id2 n i j := by
  rw [ric_add_linv, ric_smul_iso]

private lemma scalAlg_add_smul_iso (t : ℝ) (R : Curv4 n) :
    scalAlg (R + t • Iso n) = scalAlg R + t * ((n : ℝ) * ((n : ℝ) - 1)) := by
  rw [scalAlg_add_linv, scalAlg_smul_iso]

private lemma ric0_add_smul_iso (t : ℝ) (R : Curv4 n) :
    ric0 (R + t • Iso n) = ric0 R := by
  rw [ric0_add', ric0_smul', ric0_iso, smul_zero, add_zero]

/-- `∑ᵢⱼ (T · δᵢⱼ) vᵢ vⱼ = T · ∑ᵢ vᵢ²`. -/
private lemma sum_const_id2_quad (T : ℝ) (v : Fin n → ℝ) :
    (∑ i, ∑ j, T * id2 n i j * v i * v j) = T * ∑ i, v i * v i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (∑ j, T * id2 n i j * v i * v j) = T * v i * (∑ j, id2 n i j * v j) from by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; ring,
      ellinv_sum_id2_mul v i]
  ring

theorem Ccone_mono_ge_half (n : ℕ) (hn : 2 ≤ n) :
    ∀ s s' : ℝ, 1 / 2 ≤ s → s ≤ s' →
      Work.Diff.Alg.Pinch.Ccone (n := n) s' (1 / 2) (1 - 4 / ((n : ℝ) - 2 + 8 * s'))
        ⊆ Work.Diff.Alg.Pinch.Ccone (n := n) s (1 / 2) (1 - 4 / ((n : ℝ) - 2 + 8 * s)) := by
  intro s s' hs hss' Y hY
  simp only [Ccone, Set.mem_image] at hY ⊢
  obtain ⟨R, hRmem, rfl⟩ := hY
  obtain ⟨hRalg, hRpic, hRric⟩ := hRmem
  set p : ℝ := 1 - 4 / ((n : ℝ) - 2 + 8 * s) with hp
  set p' : ℝ := 1 - 4 / ((n : ℝ) - 2 + 8 * s') with hp'
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have hD : 0 < (n : ℝ) - 2 + 8 * s := by linarith
  have hD' : 0 < (n : ℝ) - 2 + 8 * s' := by linarith
  have hp_le_one : p ≤ 1 := by
    rw [hp]
    have : 0 < 4 / ((n : ℝ) - 2 + 8 * s) := div_pos (by norm_num) hD
    linarith
  have hpp' : p ≤ p' := by
    rw [hp, hp']
    have h4 : 4 / ((n : ℝ) - 2 + 8 * s') ≤ 4 / ((n : ℝ) - 2 + 8 * s) :=
      div_le_div_of_nonneg_left (by norm_num) hD (by linarith)
    linarith
  have hscal0 : 0 ≤ scalAlg R := (inPIC2_metric_basic n).2.2 R hRpic
  have hden : 0 < 1 + 2 * s * ((n : ℝ) - 1) := by
    have h := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * s) hn1
    linarith
  set t : ℝ := 2 * (s' - s) * scalAlg R / ((n : ℝ) * (1 + 2 * s * ((n : ℝ) - 1))) with ht
  have ht_nonneg : 0 ≤ t := by
    rw [ht]
    exact div_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * (s' - s)) hscal0)
      (mul_nonneg hn0.le hden.le)
  refine ⟨R + t • Iso n, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact isAlgCurv_add hRalg (isAlgCurv_smul t (Iso_algCurv n))
  · exact Cone.inPIC2_add hRpic (Cone.inPIC2_smul (Cone.inPIC2_iso n) ht_nonneg)
  · -- `RicPinch p (R + t • Iso n)`
    intro v
    have hS0 : 0 ≤ ∑ i, v i * v i := Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hsum : (∑ i, ∑ j, ric (R + t • Iso n) i j * v i * v j)
        = (∑ i, ∑ j, ric R i j * v i * v j) + (t * ((n : ℝ) - 1)) * (∑ i, v i * v i) := by
      calc (∑ i, ∑ j, ric (R + t • Iso n) i j * v i * v j)
          = ∑ i, ∑ j, (ric R i j + t * ((n : ℝ) - 1) * id2 n i j) * v i * v j := by
            apply Finset.sum_congr rfl; intro i _
            apply Finset.sum_congr rfl; intro j _
            rw [ric_add_smul_iso]
        _ = (∑ i, ∑ j, ric R i j * v i * v j)
              + ∑ i, ∑ j, t * ((n : ℝ) - 1) * id2 n i j * v i * v j := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl; intro i _
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl; intro j _
            ring
        _ = _ := by rw [sum_const_id2_quad]
    have hL : p * scalAlg (R + t • Iso n) / (n : ℝ)
        = p * scalAlg R / (n : ℝ) + p * (t * ((n : ℝ) - 1)) := by
      rw [scalAlg_add_smul_iso]
      field_simp
    have hkey : p * scalAlg R / (n : ℝ) + p * (t * ((n : ℝ) - 1))
        ≤ p' * scalAlg R / (n : ℝ) + (t * ((n : ℝ) - 1)) := by
      have e : (p' - p) * scalAlg R / (n : ℝ) + (t * ((n : ℝ) - 1)) * (1 - p)
          = p' * scalAlg R / (n : ℝ) + (t * ((n : ℝ) - 1))
            - (p * scalAlg R / (n : ℝ) + p * (t * ((n : ℝ) - 1))) := by ring
      have h1 : 0 ≤ (p' - p) * scalAlg R / (n : ℝ) :=
        div_nonneg (mul_nonneg (by linarith) hscal0) hn0.le
      have h2 : 0 ≤ (t * ((n : ℝ) - 1)) * (1 - p) :=
        mul_nonneg (mul_nonneg ht_nonneg hn1) (by linarith)
      linarith
    rw [hL, hsum]
    have hpn : p * scalAlg R / (n : ℝ) ≤ p' * scalAlg R / (n : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hpp' hscal0) hn0.le
    have hA := mul_le_mul_of_nonneg_right hpn hS0
    have hB : (p * (t * ((n : ℝ) - 1))) * (∑ i, v i * v i)
        ≤ (t * ((n : ℝ) - 1)) * (∑ i, v i * v i) :=
      mul_le_mul_of_nonneg_right (by
        have h := mul_le_mul_of_nonneg_right hp_le_one (mul_nonneg ht_nonneg hn1)
        simpa using h) hS0
    have hRic := hRric v
    rw [add_mul]
    linarith
  · -- `ℓ_{s,1/2} (R + t • Iso n) = ℓ_{s',1/2} R`
    have hc : 2 * s * scalAlg R / (n : ℝ) + t * (1 + 2 * s * ((n : ℝ) - 1))
        = 2 * s' * scalAlg R / (n : ℝ) := by
      rw [ht]
      field_simp
      ring
    rw [ell_half_add_smul_iso s t R, ell_half_eq s R, ell_half_eq s' R, add_assoc, ← add_smul, hc]

end Work.Diff.Alg.Pinch
