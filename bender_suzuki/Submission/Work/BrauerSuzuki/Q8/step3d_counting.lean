import Mathlib
import Submission.Work.BrauerSuzuki.Q8.Ctx
import Submission.Work.BrauerSuzuki.Q8.Eta
import Submission.Work.BrauerSuzuki.Q8.Eta2
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.CFun
import Submission.Work.BrauerSuzuki.Characters.sum_sum_char_eq
import Submission.Work.Clifford.Classes

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Q8

/-- Reordering a triple sum. -/
private theorem sum_sum_sum_comm' {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (g : γ → α → β → ℂ) :
    (∑ x : α, ∑ y : β, ∑ i : γ, g i x y) = ∑ i : γ, ∑ x : α, ∑ y : β, g i x y := by
  calc (∑ x : α, ∑ y : β, ∑ i : γ, g i x y)
      = ∑ x : α, ∑ i : γ, ∑ y : β, g i x y := by
        apply Finset.sum_congr rfl; intro x _; rw [Finset.sum_comm]
    _ = ∑ i : γ, ∑ x : α, ∑ y : β, g i x y := by rw [Finset.sum_comm]

/-- A constant double sum. -/
private theorem sum_sum_const' (a : ℂ) {α β : Type*} [Fintype α] [Fintype β] :
    (∑ _ : α, ∑ _ : β, a) = (Fintype.card α : ℂ) * (Fintype.card β : ℂ) * a := by
  simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

/-- Exchange a double sum with a finite sum of scalar multiples. -/
private theorem sum_sum_add' {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (a : ℂ) (f : γ → α → β → ℂ) (c : γ → ℂ) :
    (∑ x : α, ∑ y : β, (a + ∑ i : γ, c i * f i x y))
      = (∑ _ : α, ∑ _ : β, a) + ∑ i : γ, c i * (∑ x : α, ∑ y : β, f i x y) := by
  simp only [Finset.sum_add_distrib]
  rw [add_left_cancel_iff]
  rw [show (∑ x : α, ∑ y : β, ∑ i : γ, c i * f i x y)
      = ∑ i : γ, ∑ x : α, ∑ y : β, c i * f i x y from by
        calc (∑ x : α, ∑ y : β, ∑ i : γ, c i * f i x y)
            = ∑ x : α, ∑ i : γ, ∑ y : β, c i * f i x y := by
              apply Finset.sum_congr rfl; intro x _; rw [Finset.sum_comm]
          _ = ∑ i : γ, ∑ x : α, ∑ y : β, c i * f i x y := by rw [Finset.sum_comm]]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]

/-- **Glauberman (1974), step (3)(d).**  For every involution `u` of `G`,
`1 + ∑ εᵢ χᵢ(u)² / χᵢ(1) = 0`.

We count the pairs `(a, b)` of elements of the conjugacy class `C` of `u` through the vanishing
of `η` off `B` and the fact that no element of `B` has odd order, so that no element of `B` can
be a product of two involutions.  Both sides are then rewritten using the class-sum identity
`∑_{x,y ∈ C} χ(x y) = (|C| χ(u))² / χ(1)`. -/
theorem step3d_counting {G : Type*} [Group G] [Fintype G] {x : G} {S : Sylow 2 G}
    (h : Work.BrauerSuzuki.Q8.Ctx G x S) (χ : Fin 3 → G → ℂ) (ε : Fin 3 → ℂ)
    (hIrr : ∀ i, χ i ∈ Work.CharCore.Irr G)
    (hη : h.eta = (fun _ => (1 : ℂ)) + ∑ i, ε i • χ i)
    (hB : ∀ y : G, y ∈ Work.BrauerSuzuki.Q8.Bset x → ¬ Odd (orderOf y))
    (hmul : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → Odd (orderOf (a * b)))
    {u : G} (hu : orderOf u = 2) :
    (1 : ℂ) + ∑ i, ε i * (χ i u) ^ 2 / (χ i 1) = 0 := by
  let C : ConjClasses G := ConjClasses.mk u
  classical
  have huC : u ∈ C.carrier := ConjClasses.mem_carrier_mk
  -- Pointwise form of the hypothesis `η = 1 + ∑ εᵢ χᵢ`.
  have hηz : ∀ z : G, h.eta z = 1 + ∑ i, ε i * χ i z := by
    intro z
    have h1 := congrFun hη z
    simpa only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply] using h1
  -- Every element of the conjugacy class of the involution `u` is an involution.
  have hord : ∀ a : C.carrier, orderOf (a : G) = 2 := by
    intro a
    have ha : ConjClasses.mk (a : G) = ConjClasses.mk u :=
      ConjClasses.mem_carrier_iff_mk_eq.mp a.2
    obtain ⟨g, hg⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp ha)
    calc orderOf (a : G) = orderOf ((MulAut.conj g) (a : G)) :=
          (MulEquiv.orderOf_eq (MulAut.conj g) (a : G)).symm
      _ = orderOf (g * (a : G) * g⁻¹) := by rw [MulAut.conj_apply]
      _ = orderOf u := by rw [hg]
      _ = 2 := hu
  -- The class-sum identity for each irreducible constituent.
  have hchi : ∀ i : Fin 3, (∑ a : C.carrier, ∑ b : C.carrier, χ i ((a : G) * (b : G)))
      = ((Fintype.card C.carrier : ℂ) * χ i u) ^ 2 / χ i 1 := by
    intro i
    rw [Work.BrauerSuzuki.Characters.sum_sum_char_eq (hIrr i) C, Nat.card_eq_fintype_card]
    have hrep : χ i (Work.CharCore.rep C) = χ i u :=
      (Work.CharCore.IsClassFun.eq_rep (Work.CharCore.isClassFun_of_mem_Irr (hIrr i)) huC).symm
    rw [hrep]
  -- `η` vanishes on products of two involutions.
  have hsum0 : (∑ a : C.carrier, ∑ b : C.carrier, h.eta ((a : G) * (b : G))) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    refine h.eta_apply_notMem_Bset (fun hmem => ?_)
    exact hB _ hmem (hmul (a : G) (b : G) (hord a) (hord b))
  -- Expansion of the same double sum through the decomposition of `η`.
  have hexpand : (∑ a : C.carrier, ∑ b : C.carrier, h.eta ((a : G) * (b : G)))
      = (Fintype.card C.carrier : ℂ) * (Fintype.card C.carrier : ℂ)
        + ∑ i, ε i * (((Fintype.card C.carrier : ℂ) * χ i u) ^ 2 / χ i 1) := by
    calc (∑ a : C.carrier, ∑ b : C.carrier, h.eta ((a : G) * (b : G)))
        = ∑ a : C.carrier, ∑ b : C.carrier, (1 + ∑ i, ε i * χ i ((a : G) * (b : G))) := by
          apply Finset.sum_congr rfl; intro a _
          apply Finset.sum_congr rfl; intro b _
          exact hηz _
      _ = (∑ _ : C.carrier, ∑ _ : C.carrier, (1 : ℂ))
            + ∑ i, ε i * (∑ a : C.carrier, ∑ b : C.carrier, χ i ((a : G) * (b : G))) :=
          sum_sum_add' (α := C.carrier) (β := C.carrier)
            (1 : ℂ) (fun i a b => χ i ((a : G) * (b : G))) ε
      _ = (Fintype.card C.carrier : ℂ) * (Fintype.card C.carrier : ℂ)
            + ∑ i, ε i * (((Fintype.card C.carrier : ℂ) * χ i u) ^ 2 / χ i 1) := by
          rw [sum_sum_const' (1 : ℂ), mul_one, add_left_cancel_iff]
          apply Finset.sum_congr rfl
          intro i _
          rw [hchi i]
  -- Combine the two evaluations.
  have hzero : (Fintype.card C.carrier : ℂ) * (Fintype.card C.carrier : ℂ)
      + ∑ i, ε i * (((Fintype.card C.carrier : ℂ) * χ i u) ^ 2 / χ i 1) = 0 := by
    rw [← hexpand, hsum0]
  have hfac : (∑ i, ε i * (((Fintype.card C.carrier : ℂ) * χ i u) ^ 2 / χ i 1))
      = (Fintype.card C.carrier : ℂ) ^ 2 * (∑ i, ε i * (χ i u) ^ 2 / χ i 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hmain : (Fintype.card C.carrier : ℂ) ^ 2
      * (1 + ∑ i, ε i * (χ i u) ^ 2 / χ i 1) = 0 := by
    rw [show (Fintype.card C.carrier : ℂ) ^ 2 * (1 + ∑ i, ε i * (χ i u) ^ 2 / χ i 1)
        = (Fintype.card C.carrier : ℂ) * (Fintype.card C.carrier : ℂ)
          + (Fintype.card C.carrier : ℂ) ^ 2 * (∑ i, ε i * (χ i u) ^ 2 / χ i 1) from by ring]
    rw [hfac] at hzero
    exact hzero
  have hN : (Fintype.card C.carrier : ℂ) ≠ 0 := by
    have hpos : 0 < Fintype.card C.carrier := Fintype.card_pos_iff.mpr ⟨⟨u, huC⟩⟩
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hpos)
  exact (mul_eq_zero.mp hmain).resolve_left (pow_ne_zero 2 hN)

end Work.BrauerSuzuki.Q8
