import Mathlib
import Submission.Work.Peluse.BoxNorm.winForm_shift_sum_star
import Submission.Work.Peluse.BoxNorm.winForm_succ_prod_sum

namespace Work.Peluse.BoxNorm

/-- Cauchy--Schwarz step of the Gowers--Cauchy--Schwarz induction for the box form.

Route: expand `winForm (n+1)` with `winForm_succ`, then both sides with `simp only [winForm]`;
split each `ω`-product at the first coordinate using `cube_prod_mul_star` (in `WinAux`) so the
cube term becomes `Gf a' · conj (Gt a)` with
`Gf a' := ∏ ω, star^[weight ω] (φ (Fin.cases false ω) (x + σ(corner z z' ω) + a'.1))` and
`Gt a := ∏ ω, star^[weight ω] (φ (Fin.cases true ω) (x + σ(corner z z' ω) + a.1))`;
sum `Gf a' * conj (Gt a)` over `(a,a')` to `(∑ a' Gf a') * conj (∑ a Gt a)`; apply
`cauchySchwarzC` over the joint index `(z, z', x)` (a Finset
`(Finset.univ : Finset (Tuple n Q' × Tuple n Q')) ×ˢ W`); and identify
`∑_{z,z',x} |∑_{a'} Gf a'|²` with the "false" sum of `winForm n`'s via `pairSum_star` and
`winForm_shift_prod` (in `WinAux`). -/
theorem winForm_succ_cs {n : ℕ} (Q : Fin (n+1) → Finset ℤ) (W : Finset ℤ)
    (φ : (Fin (n+1) → Bool) → ℤ → ℂ) :
    ‖Work.Peluse.BoxNorm.winForm (n+1) Q W φ‖ ^ 2
      ≤ ‖(∑ a : {x : ℤ // x ∈ Q 0}, ∑ a' : {x : ℤ // x ∈ Q 0},
          Work.Peluse.BoxNorm.winForm n (fun i : Fin n => Q i.succ) W
            (fun ω y => φ (Fin.cases false ω) (y + a.1) * star (φ (Fin.cases false ω) (y + a'.1))))‖
        * ‖(∑ a : {x : ℤ // x ∈ Q 0}, ∑ a' : {x : ℤ // x ∈ Q 0},
          Work.Peluse.BoxNorm.winForm n (fun i : Fin n => Q i.succ) W
            (fun ω y => φ (Fin.cases true ω) (y + a.1) * star (φ (Fin.cases true ω) (y + a'.1))))‖ := by
  classical
  let S : Finset ((Tuple n (fun i : Fin n => Q i.succ) × Tuple n (fun i : Fin n => Q i.succ)) × ℤ) :=
    (Finset.univ : Finset (Tuple n (fun i : Fin n => Q i.succ) × Tuple n (fun i : Fin n => Q i.succ))) ×ˢ W
  let U : (Tuple n (fun i : Fin n => Q i.succ) × Tuple n (fun i : Fin n => Q i.succ)) × ℤ → ℂ :=
    fun i => ∑ a' : {x : ℤ // x ∈ Q 0},
      halfProd n (fun i : Fin n => Q i.succ) (slotF φ) i.1.1 i.1.2 i.2 a'.1
  let V : (Tuple n (fun i : Fin n => Q i.succ) × Tuple n (fun i : Fin n => Q i.succ)) × ℤ → ℂ :=
    fun i => ∑ a : {x : ℤ // x ∈ Q 0},
      halfProd n (fun i : Fin n => Q i.succ) (slotT φ) i.1.1 i.1.2 i.2 a.1
  have hL : winForm (n+1) Q W φ = ∑ i ∈ S, U i * star (V i) := by
    rw [winForm_succ_prod_sum (n := n) Q W φ]
    exact (Finset.sum_product (Finset.univ :
      Finset (Tuple n (fun i : Fin n => Q i.succ) × Tuple n (fun i : Fin n => Q i.succ))) W
        (fun i => U i * star (V i))).symm
  have hfalse : ‖(∑ a : {x : ℤ // x ∈ Q 0}, ∑ a' : {x : ℤ // x ∈ Q 0},
          winForm n (fun i : Fin n => Q i.succ) W
            (fun ω y => φ (Fin.cases false ω) (y + a.1) * star (φ (Fin.cases false ω) (y + a'.1))))‖
        = ∑ i ∈ S, ‖U i‖ ^ 2 := by
    have h1 : (∑ a : {x : ℤ // x ∈ Q 0}, ∑ a' : {x : ℤ // x ∈ Q 0},
          winForm n (fun i : Fin n => Q i.succ) W
            (fun ω y => φ (Fin.cases false ω) (y + a.1) * star (φ (Fin.cases false ω) (y + a'.1))))
        = (∑ a : {x : ℤ // x ∈ Q 0}, ∑ a' : {x : ℤ // x ∈ Q 0},
          winForm n (fun i : Fin n => Q i.succ) W
            (fun ω y => slotF φ ω (y + a.1) * star (slotF φ ω (y + a'.1)))) := by
      simp only [slotF]
    rw [h1, winForm_shift_sum_star (n := n) (Q := fun i : Fin n => Q i.succ) W (slotF φ)
      (fun a : {x : ℤ // x ∈ Q 0} => a.1)]
    have hsplit : (∑ p : Tuple n (fun i : Fin n => Q i.succ) × Tuple n (fun i : Fin n => Q i.succ),
        ∑ x ∈ W, ((‖∑ a : {x : ℤ // x ∈ Q 0},
            halfProd n (fun i : Fin n => Q i.succ) (slotF φ) p.1 p.2 x (a.1)‖ ^ 2 : ℝ) : ℂ))
        = ∑ i ∈ S, ((‖U i‖ ^ 2 : ℝ) : ℂ) :=
      (Finset.sum_product (Finset.univ :
        Finset (Tuple n (fun i : Fin n => Q i.succ) × Tuple n (fun i : Fin n => Q i.succ))) W
          (fun i => ((‖U i‖ ^ 2 : ℝ) : ℂ))).symm
    rw [hsplit]
    exact norm_ofReal_sum_eq S (fun i => ‖U i‖ ^ 2) (fun i _ => sq_nonneg _)
  have htrue : ‖(∑ a : {x : ℤ // x ∈ Q 0}, ∑ a' : {x : ℤ // x ∈ Q 0},
          winForm n (fun i : Fin n => Q i.succ) W
            (fun ω y => φ (Fin.cases true ω) (y + a.1) * star (φ (Fin.cases true ω) (y + a'.1))))‖
        = ∑ i ∈ S, ‖V i‖ ^ 2 := by
    have h1 : (∑ a : {x : ℤ // x ∈ Q 0}, ∑ a' : {x : ℤ // x ∈ Q 0},
          winForm n (fun i : Fin n => Q i.succ) W
            (fun ω y => φ (Fin.cases true ω) (y + a.1) * star (φ (Fin.cases true ω) (y + a'.1))))
        = (∑ a : {x : ℤ // x ∈ Q 0}, ∑ a' : {x : ℤ // x ∈ Q 0},
          winForm n (fun i : Fin n => Q i.succ) W
            (fun ω y => slotT φ ω (y + a.1) * star (slotT φ ω (y + a'.1)))) := by
      simp only [slotT]
    rw [h1, winForm_shift_sum_star (n := n) (Q := fun i : Fin n => Q i.succ) W (slotT φ)
      (fun a : {x : ℤ // x ∈ Q 0} => a.1)]
    have hsplit : (∑ p : Tuple n (fun i : Fin n => Q i.succ) × Tuple n (fun i : Fin n => Q i.succ),
        ∑ x ∈ W, ((‖∑ a : {x : ℤ // x ∈ Q 0},
            halfProd n (fun i : Fin n => Q i.succ) (slotT φ) p.1 p.2 x (a.1)‖ ^ 2 : ℝ) : ℂ))
        = ∑ i ∈ S, ((‖V i‖ ^ 2 : ℝ) : ℂ) :=
      (Finset.sum_product (Finset.univ :
        Finset (Tuple n (fun i : Fin n => Q i.succ) × Tuple n (fun i : Fin n => Q i.succ))) W
          (fun i => ((‖V i‖ ^ 2 : ℝ) : ℂ))).symm
    rw [hsplit]
    exact norm_ofReal_sum_eq S (fun i => ‖V i‖ ^ 2) (fun i _ => sq_nonneg _)
  rw [hL, hfalse, htrue]
  exact cauchySchwarzC S U V


end Work.Peluse.BoxNorm
