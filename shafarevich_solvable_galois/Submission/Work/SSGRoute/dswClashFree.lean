import Mathlib
import Submission.Work.SSGRoute.prop5.nestedLieDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Specht–Wever / Dynkin: the left-nested bracket map acts as `j` on the degree-`j` Lie part

Let `A = FreeAssoc X = ℤ[FreeMonoid X]` be the free associative `ℤ`-algebra on `X`.  The
left-nested bracket monomial of a word `w = x₁…x_j` is
`lnMon w = [[…[x₁,x₂],…],x_j]`, and `lieSpan X j` is the `ℤ`-span of the bracket monomials of
degree `j` (the degree-`j` part of the free Lie ring).

The Specht–Wever (Dynkin) identity states that any `ℤ`-linear map `L` with
`L (wordEl w) = lnMon w` for every word `w` satisfies `L x = j • x` for `x ∈ lieSpan X j`.

The proof formalised here is the classical one, phrased in terms of the anti-homomorphism
`Φ : A → End(A)` determined on words by
`Φ (x₁…x_q) = ad'_{x_q} ∘ … ∘ ad'_{x₁}`,   `ad'_y U = U * wordEl [y] - wordEl [y] * U`.
The two ingredients are

* `L_mul_brkMon`: for `u` in the augmentation ideal (`filz X 1`) and a bracket monomial `b`,
  `L (u * b) = Φ b (L u)` (proved by structural induction on the bracket tree, using that
  `L (u * wordEl [y]) = ad'_y (L u)`);
* `Phi_brkMon`: `Φ b (a) = a * b - b * a` for a bracket monomial `b` (again by structural
  induction, using the defining anti-multiplicativity of `Φ` and the Jacobi identity).

For a bracket monomial `[u, w] = u w - w u` of degree `p + q` the two give
`L [u,w] = Φ w (L u) - Φ u (L w) = p (u w - w u) - q (w u - u w) = (p+q) [u,w]`,
which is the induction step.
-/

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute

namespace DSWC

open Work.SSGRoute.prop5

variable {X : Type*}

/-! ## The anti-homomorphism `Φ` -/

/-- `adR y U = U * wordEl [y] - wordEl [y] * U`; the "right" adjoint operator. -/
def adR (y : X) : Module.End ℤ (FreeAssoc X) :=
  LinearMap.mulRight ℤ (wordEl [y]) - LinearMap.mulLeft ℤ (wordEl [y])

theorem adR_apply (y : X) (U : FreeAssoc X) :
    adR y U = U * wordEl [y] - wordEl [y] * U := by
  simp [adR, LinearMap.mulRight_apply, LinearMap.mulLeft_apply]

/-- The algebra homomorphism into the opposite algebra determined by `x ↦ adR x`.  Composing
with `MulOpposite.unop` gives the anti-homomorphism `Φ`. -/
def Evr : FreeAssoc X →ₐ[ℤ] (Module.End ℤ (FreeAssoc X))ᵐᵒᵖ :=
  MonoidAlgebra.lift ℤ (Module.End ℤ (FreeAssoc X))ᵐᵒᵖ (FreeMonoid X)
    (FreeMonoid.lift (fun y : X => MulOpposite.op (adR y)))

/-- The anti-homomorphism `Φ : FreeAssoc X → End (FreeAssoc X)`. -/
def Phi (v : FreeAssoc X) : Module.End ℤ (FreeAssoc X) := (Evr v).unop

theorem Evr_single (a : FreeMonoid X) (b : ℤ) :
    Evr (MonoidAlgebra.single a b) =
      b • FreeMonoid.lift (fun y : X => MulOpposite.op (adR y)) a :=
  MonoidAlgebra.lift_single _ a b

theorem Phi_add (a b : FreeAssoc X) : Phi (a + b) = Phi a + Phi b := by
  simp only [Phi, map_add, MulOpposite.unop_add]

theorem Phi_sub (a b : FreeAssoc X) : Phi (a - b) = Phi a - Phi b := by
  simp only [Phi, map_sub, MulOpposite.unop_sub]

theorem Phi_mul (a b : FreeAssoc X) : Phi (a * b) = Phi b * Phi a := by
  simp only [Phi, map_mul, MulOpposite.unop_mul]

theorem Phi_one : Phi (1 : FreeAssoc X) = 1 := by
  simp only [Phi, map_one, MulOpposite.unop_one]

theorem Phi_smul (c : ℤ) (a : FreeAssoc X) : Phi (c • a) = c • Phi a := by
  simp only [Phi, map_smul, MulOpposite.unop_smul]

theorem Phi_wordEl_singleton (y : X) : Phi (wordEl [y]) = adR y := by
  have h : wordEl [y] = MonoidAlgebra.single (FreeMonoid.of y) (1 : ℤ) := rfl
  rw [h]
  show (Evr (MonoidAlgebra.single (FreeMonoid.of y) (1 : ℤ))).unop = adR y
  rw [Evr_single, one_smul, FreeMonoid.lift_eval_of]
  rfl

/-! ## Elementary word manipulations -/

theorem lnMon_append_singleton (x : X) (u : List X) (y : X) :
    lnMon (x :: (u ++ [y])) = lnMon (x :: u) * wordEl [y] - wordEl [y] * lnMon (x :: u) := by
  simp only [lnMon, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem wordEl_append (u v : List X) : wordEl (u ++ v) = wordEl u * wordEl v := by
  rw [wordEl, wordEl, wordEl, FreeMonoid.ofList_append, MonoidAlgebra.single_mul_single,
    one_mul]

theorem lnMon_singleton (y : X) : lnMon [y] = wordEl [y] := rfl

/-- `lnMon` of a nonempty word appended by one letter. -/
theorem lnMon_append_singleton' {v : List X} (hv : v ≠ []) (y : X) :
    lnMon (v ++ [y]) = lnMon v * wordEl [y] - wordEl [y] * lnMon v := by
  cases v with
  | nil => exact absurd rfl hv
  | cons x u => exact lnMon_append_singleton x u y

theorem wordEl_toList (w : FreeMonoid X) :
    wordEl (FreeMonoid.toList w) = MonoidAlgebra.single w (1 : ℤ) := by
  rw [wordEl, FreeMonoid.ofList_toList]

/-! ## `L` on a right multiple by a letter -/

/-- On the augmentation ideal `filz X 1`, right multiplication by a letter turns into the
adjoint operator `adR` after applying `L`. -/
theorem L_mul_wordEl (L : FreeAssoc X →ₗ[ℤ] FreeAssoc X)
    (hL : ∀ w : List X, L (wordEl w) = lnMon w)
    {u : FreeAssoc X} (hu : u ∈ filz X 1) (y : X) :
    L (u * wordEl [y]) = adR y (L u) := by
  refine Submodule.span_induction (p := fun u _ => L (u * wordEl [y]) = adR y (L u))
    ?_ ?_ ?_ ?_ hu
  · rintro a ⟨w, hw, rfl⟩
    have hwne : FreeMonoid.toList w ≠ [] := by
      rintro h
      have h1 : w = 1 := FreeMonoid.toList.injective (by rw [h, FreeMonoid.toList_one])
      rw [h1] at hw
      simp at hw
    rw [← wordEl_toList, ← wordEl_append, hL, hL, adR_apply, lnMon_append_singleton' hwne y]
  · simp
  · intro a b _ _ ha hb
    rw [add_mul, L.map_add, ha, hb, L.map_add, (adR y).map_add]
  · intro c a _ ha
    rw [smul_mul_assoc, L.map_smul, ha, L.map_smul, (adR y).map_smul]

/-! ## `L (u * b)` for a bracket monomial `b` -/

/-- For `u` in the augmentation ideal and a bracket monomial `b`, `L (u * b) = Φ b (L u)`. -/
theorem L_mul_brkMon (L : FreeAssoc X →ₗ[ℤ] FreeAssoc X)
    (hL : ∀ w : List X, L (wordEl w) = lnMon w) (c : Magma X) :
    ∀ (u : FreeAssoc X), u ∈ filz X 1 →
      L (u * brkMon X c) = Phi (brkMon X c) (L u) := by
  induction c with
  | gen y =>
      intro u hu
      rw [brkMon_gen, Phi_wordEl_singleton]
      exact L_mul_wordEl L hL hu y
  | mul c1 c2 ih1 ih2 =>
      intro u hu
      rw [brkMon_mul]
      have h1 : u * brkMon X c1 ∈ filz X 1 := mul_mem_filz' X 1 (brkMon X c1) hu
      have h2 : u * brkMon X c2 ∈ filz X 1 := mul_mem_filz' X 1 (brkMon X c2) hu
      rw [show u * (brkMon X c1 * brkMon X c2 - brkMon X c2 * brkMon X c1)
            = (u * brkMon X c1) * brkMon X c2 - (u * brkMon X c2) * brkMon X c1 from by
            noncomm_ring]
      rw [L.map_sub, ih2 (u * brkMon X c1) h1, ih1 (u * brkMon X c2) h2,
        ih1 u hu, ih2 u hu]
      rw [Phi_sub, Phi_mul, Phi_mul, LinearMap.sub_apply, Module.End.mul_apply,
        Module.End.mul_apply]

/-! ## `Φ` on a bracket monomial -/

/-- `Φ b (a) = a * b - b * a` for a bracket monomial `b` (the "left bracketing" identity). -/
theorem Phi_brkMon (c : Magma X) :
    ∀ (a : FreeAssoc X), Phi (brkMon X c) a = a * brkMon X c - brkMon X c * a := by
  induction c with
  | gen y =>
      intro a
      rw [brkMon_gen, Phi_wordEl_singleton, adR_apply]
  | mul c1 c2 ih1 ih2 =>
      intro a
      rw [brkMon_mul, Phi_sub, Phi_mul, Phi_mul, LinearMap.sub_apply, Module.End.mul_apply,
        Module.End.mul_apply]
      rw [ih1 a, ih2 a, ih2 (a * brkMon X c1 - brkMon X c1 * a),
        ih1 (a * brkMon X c2 - brkMon X c2 * a)]
      noncomm_ring

/-! ## The augmentation ideal membership of bracket monomials -/

theorem Magma_size_pos (c : Magma X) : 0 < Magma.size c := by
  induction c with
  | gen y => rw [Magma.size_gen]; omega
  | mul a b iha ihb => rw [Magma.size_mul]; omega

theorem brkMon_mem_filz_one (c : Magma X) : brkMon X c ∈ filz X 1 := by
  induction c with
  | gen y =>
      rw [brkMon_gen]
      exact Submodule.subset_span
        ⟨FreeMonoid.of y, by rw [FreeMonoid.length_of],
         by rw [wordEl, FreeMonoid.ofList_singleton]⟩
  | mul a b iha ihb =>
      rw [brkMon_mul]
      exact Submodule.sub_mem _
        (mul_mem_filz' X 1 (brkMon X b) iha) (mul_mem_filz' X 1 (brkMon X a) ihb)

/-! ## The main induction -/

/-- The Specht–Wever identity with `ℤ`-scalars. -/
theorem nestedBracket_aux (L : FreeAssoc X →ₗ[ℤ] FreeAssoc X)
    (hL : ∀ w : List X, L (wordEl w) = lnMon w) :
    ∀ (j : ℕ) (x : FreeAssoc X), x ∈ lieSpan X j → L x = (j : ℤ) • x := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro x hx
    refine Submodule.span_induction (p := fun x _ => L x = (j : ℤ) • x) ?_ ?_ ?_ ?_ hx
    · rintro a ⟨c, hc, rfl⟩
      cases c with
      | gen y =>
          have hj : j = 1 := by rw [← hc, Magma.size_gen]
          rw [brkMon_gen, hj, hL, lnMon_singleton]
          simp
      | mul c1 c2 =>
          rw [Magma.size_mul] at hc
          have hp : Magma.size c1 < j := by have := Magma_size_pos c2; omega
          have hq : Magma.size c2 < j := by have := Magma_size_pos c1; omega
          have hm1 : brkMon X c1 ∈ lieSpan X (Magma.size c1) :=
            Submodule.subset_span ⟨c1, rfl, rfl⟩
          have hm2 : brkMon X c2 ∈ lieSpan X (Magma.size c2) :=
            Submodule.subset_span ⟨c2, rfl, rfl⟩
          have hf1 : brkMon X c1 ∈ filz X 1 := brkMon_mem_filz_one c1
          have hf2 : brkMon X c2 ∈ filz X 1 := brkMon_mem_filz_one c2
          rw [brkMon_mul, L.map_sub, L_mul_brkMon L hL c2 (brkMon X c1) hf1,
            L_mul_brkMon L hL c1 (brkMon X c2) hf2,
            ih (Magma.size c1) hp (brkMon X c1) hm1, ih (Magma.size c2) hq (brkMon X c2) hm2]
          rw [(Phi (brkMon X c2)).map_smul, (Phi (brkMon X c1)).map_smul]
          rw [Phi_brkMon c2 (brkMon X c1), Phi_brkMon c1 (brkMon X c2)]
          set Y := brkMon X c1 * brkMon X c2 - brkMon X c2 * brkMon X c1 with hY
          rw [show brkMon X c2 * brkMon X c1 - brkMon X c1 * brkMon X c2 = -Y from by
            rw [hY]; noncomm_ring]
          rw [smul_neg, sub_neg_eq_add, ← add_smul, ← hc, Nat.cast_add]
    · simp
    · intro a b _ _ ha hb
      rw [L.map_add, ha, hb, ← smul_add]
    · intro c a _ ha
      rw [L.map_smul, ha, smul_comm]

end DSWC

theorem nestedBracket_dswC (X : Type*) (j : ℕ)
    (L : Work.SSGRoute.prop5.FreeAssoc X →ₗ[ℤ] Work.SSGRoute.prop5.FreeAssoc X)
    (hL : ∀ w : List X, L (Work.SSGRoute.prop5.wordEl w) = Work.SSGRoute.prop5.lnMon w)
    {x : Work.SSGRoute.prop5.FreeAssoc X} (hx : x ∈ Work.SSGRoute.prop5.lieSpan X j) :
    L x = j • x := by
  have h := DSWC.nestedBracket_aux L hL j x hx
  rw [← Nat.cast_smul_eq_nsmul ℤ j x]
  exact h

end Work.SSGRoute
