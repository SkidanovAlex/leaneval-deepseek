import Mathlib
import Submission.Work.WilE3K.ET
import Submission.Work.WilE3K.Defs
import Submission.Work.WilE3K.LiftEntry
import Submission.Work.WilE3K.Branch
import Submission.Work.WilE3.Sep
import Submission.Work.WilE3.Defs

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilE3K
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

variable {n r : ℕ}

/-- The image of a convex set of `ℝⁿ` under an affine form is convex. -/
theorem convex_ell_image (S : Work.WilE3.SepChainLocal n r) (j : Fin r) {D : Set (Fin n → ℝ)}
    (hD : Convex ℝ D) : Convex ℝ (Lift.ell S j '' D) := by
  rintro _ ⟨x1, hx1, rfl⟩ _ ⟨x2, hx2, rfl⟩ a b ha hb hab
  refine ⟨a • x1 + b • x2, hD hx1 hx2 ha hb hab, ?_⟩
  have h1 : Lift.ell S j (a • x1 + b • x2) = a * Lift.ell S j x1 + b * Lift.ell S j x2 := by
    have hsum : (∑ i, S.a j i * (a * x1 i + b * x2 i))
        = a * (∑ i, S.a j i * x1 i) + b * (∑ i, S.a j i * x2 i) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [Lift.ell, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsum]
    linear_combination (-(S.b j)) * hab
  rw [h1, smul_eq_mul, smul_eq_mul]

theorem exists_lift {n r : ℕ} (S : Work.WilE3.SepChainLocal n r)
    (f : Fin n → WilkiesDesign.E.EAPoly n r) (D : Set (Fin n → ℝ)) (s : Finset (Fin n → ℝ))
    (hpos : 0 < n)
    (htype : ∀ j, (S.phi j = Real.exp ∧ S.R j = MvPolynomial.X 0) ∨
      (S.phi j = Real.tan ∧ S.R j = 1 + MvPolynomial.X 0 ^ 2))
    (hD : Convex ℝ D)
    (hdom : ∀ x ∈ D, ∀ j, (∑ i, S.a j i * x i + S.b j) ∈ S.dom j)
    (hsD : (↑s : Set (Fin n → ℝ)) ⊆ D)
    (hnd : ∀ x ∈ s, Work.WilE3.SepChainLocal.Nondegen S f x) :
    ∃ (rt re : ℕ) (E : Work.WilE3K.ETData (rt + n - 1) rt n re)
      (t : Finset (Fin ((rt + n - 1) + 1) → ℝ)),
      rt + re = r ∧ t.card = s.card ∧ (∀ z ∈ t, E.Nondegen z) ∧
      (∑ i, WilkiesDesign.E.atomDeg (E.G i)) ≤ (∑ i, WilkiesDesign.E.atomDeg (f i)) := by
  classical
  have hn : Lift.rt S + n = (Lift.rt S + n - 1) + 1 := by omega
  -- `cos` does not vanish on `dom`
  have hcos : ∀ (p : Fin (Lift.rt S)), ∀ y ∈ S.dom (Lift.tanIdx S p), Real.cos y ≠ 0 := by
    intro p y hy
    have hd : DifferentiableAt ℝ (S.phi (Lift.tanIdx S p)) y :=
      (S.hderiv (Lift.tanIdx S p) y hy).differentiableAt
    rw [Lift.phi_tanIdx S p] at hd
    exact (Real.differentiableAt_tan).mp hd
  -- the branch constants
  have hk : ∀ p : Fin (Lift.rt S), ∃ k : ℤ, ∀ x ∈ s,
      Lift.ell S (Lift.tanIdx S p) x - (k : ℝ) * Real.pi ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    intro p
    obtain ⟨k, hk⟩ := exists_branch_sub (convex_ell_image S (Lift.tanIdx S p) hD)
      (fun y hy => by
        obtain ⟨x, hx, rfl⟩ := hy
        exact hcos p _ (hdom x hx (Lift.tanIdx S p)))
    exact ⟨k, fun x hx => hk _ ⟨x, hsD hx, rfl⟩⟩
  let k : Fin (Lift.rt S) → ℤ := fun p => Classical.choose (hk p)
  have hkspec : ∀ (p : Fin (Lift.rt S)) (x : Fin n → ℝ), x ∈ s →
      Lift.ell S (Lift.tanIdx S p) x - (k p : ℝ) * Real.pi ∈
        Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := fun p => Classical.choose_spec (hk p)
  let E := Lift.liftET S hn f k
  refine ⟨Lift.rt S, Lift.re S, E, s.image (fun x => Lift.liftPoint S E x),
    Lift.rt_add_re S, ?_, ?_, ?_⟩
  · exact Finset.card_image_of_injective s (liftPoint_injective S E)
  · intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hxs, rfl⟩ := hz
    have hxdom : ∀ j, Lift.ell S j x ∈ S.dom j := fun j => hdom x (hsD hxs) j
    refine ⟨?_, ?_, ?_⟩
    · intro i
      rw [evP_liftPoint_self (S := S) htype hn f k i x]
      exact (hnd x hxs).1 i
    · intro p
      have hpt : Lift.liftPoint S E x (E.tanCoord p) = Lift.liftT S x p :=
        Lift.liftPoint_tan S E x p
      have hlin : E.lin p (Lift.liftPoint S E x)
          = Lift.ell S (Lift.tanIdx S p) x - (k p : ℝ) * Real.pi := by
        simp only [ETData.lin]
        rw [show E = Lift.liftET S hn f k from rfl]
        simp only [Lift.liftET, Lift.liftE, Lift.liftLam, Lift.liftMu, Lift.liftPoint_free,
          Lift.ell]
        ring
      have hkey := hkspec p x hxs
      rw [ETData.tanFun, hpt, hlin]
      have h1 : Lift.liftT S x p
          = Real.tan (Lift.ell S (Lift.tanIdx S p) x - (k p : ℝ) * Real.pi) := by
        rw [Lift.liftT]
        rw [show Lift.ell S (Lift.tanIdx S p) x - (k p : ℝ) * Real.pi
            = Lift.ell S (Lift.tanIdx S p) x + ((-(k p) : ℤ) : ℝ) * Real.pi from by
          push_cast; ring]
        rw [Real.tan_add_int_mul_pi]
      rw [h1, Real.arctan_tan hkey.1 hkey.2, sub_self]
    · exact jac_det_ne_zero hn f k x
        (fun i a => ev_d_eq (S := S) htype hn f k x hxdom i a) (hnd x hxs).2
  · apply Finset.sum_le_sum
    intro i _
    exact atomDeg_liftG_le hn (Lift.cls S) f i

end Work.WilE3K
