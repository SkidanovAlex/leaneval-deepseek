import Mathlib
import Submission.Work.Pi6.EMM2.Statements
import Submission.Work.Pi6.EMM2.mulCommPropagation
import Submission.Work.Pi6.EMM2.mulCommPageTwo
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

/-!
# Graded commutativity of the product of the mod-2 Serre spectral sequence (`Work.Pi6.EMM2.mulComm`)

Over `𝔽₂` all signs of the Koszul product vanish, so the product on every page of a multiplicative
Serre spectral sequence is commutative.

**Reduction.**  The multiplicativity clause of `IsSerreMSS` pins the product on page two of the
pure tensors of the `E₂`-decomposition; bilinearity (`pageTwo_std`) and the two-slot transport
`mul_transport2` together with the normalisation of the bidegree (`pageTwo_general`) give page-two
commutativity for arbitrary elements and arbitrary nonnegative bidegrees; `mulCommPropagation`
then propagates it to every page `r ≥ 2`.

The two ingredients `pageTwo_std` and `pageTwo_general` below are proved here; the page-two
multiplicativity clause computation (`Work.Pi6.EMM2.mulCommPageTwo`) and the propagation
(`Work.Pi6.EMM2.mulCommPropagation`) are separate lemmas.
-/

namespace Work.Pi6.EMM2

open CategoryTheory CategoryTheory.Limits

variable {𝕜 : Type} [Field 𝕜]


/-! ## Bilinearity tools -/

theorem tensor_linearMap_eq_zero {M X Y : Type*} [AddCommGroup M] [Module 𝕜 M]
    [AddCommMonoid X] [Module 𝕜 X] [AddCommMonoid Y] [Module 𝕜 Y]
    (f : TensorProduct 𝕜 X Y →ₗ[𝕜] M) (h : ∀ x y, f (x ⊗ₜ[𝕜] y) = 0) : f = 0 := by
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact h x y
  | add u v hu hv => rw [map_add, hu, hv]; simp

theorem linearMap_eq_zero_of_tensor_inv {M P X Y : Type*} [AddCommGroup M] [Module 𝕜 M]
    [AddCommGroup P] [Module 𝕜 P] [AddCommMonoid X] [Module 𝕜 X] [AddCommMonoid Y] [Module 𝕜 Y]
    (e : P ≃ₗ[𝕜] TensorProduct 𝕜 X Y) (f : P →ₗ[𝕜] M)
    (h : ∀ x y, f (e.symm (x ⊗ₜ[𝕜] y)) = 0) : f = 0 := by
  have hg : f.comp e.symm.toLinearMap = 0 := tensor_linearMap_eq_zero (f.comp e.symm.toLinearMap) h
  apply LinearMap.ext
  intro p
  have hp : (f.comp e.symm.toLinearMap) (e p) = f p := by
    rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]
  rw [← hp, hg]
  simp

theorem bilin_eq_zero_of_pure {M P P' X Y X' Y' : Type*} [AddCommGroup M] [Module 𝕜 M]
    [AddCommGroup P] [Module 𝕜 P] [AddCommGroup P'] [Module 𝕜 P']
    [AddCommMonoid X] [Module 𝕜 X] [AddCommMonoid Y] [Module 𝕜 Y]
    [AddCommMonoid X'] [Module 𝕜 X'] [AddCommMonoid Y'] [Module 𝕜 Y']
    (e : P ≃ₗ[𝕜] TensorProduct 𝕜 X Y) (e' : P' ≃ₗ[𝕜] TensorProduct 𝕜 X' Y')
    (Φ : P →ₗ[𝕜] P' →ₗ[𝕜] M)
    (h : ∀ x y x' y', Φ (e.symm (x ⊗ₜ[𝕜] y)) (e'.symm (x' ⊗ₜ[𝕜] y')) = 0) : Φ = 0 := by
  apply LinearMap.ext
  intro p
  have h1 : Φ p = 0 :=
    linearMap_eq_zero_of_tensor_inv e' (Φ p) (fun x' y' => by
      have h2 : Φ.flip (e'.symm (x' ⊗ₜ[𝕜] y')) = 0 :=
        linearMap_eq_zero_of_tensor_inv e (Φ.flip (e'.symm (x' ⊗ₜ[𝕜] y'))) (fun x y => by
          rw [LinearMap.flip_apply]; exact h x y x' y')
      rw [← LinearMap.flip_apply]
      exact congrFun (congrArg DFunLike.coe h2) p)
  rw [h1]
  rfl

/-! ## Transport tools -/

/-- Two transported elements are equal if their transports are. -/
theorem eqRec_inj {α : Sort*} {F : α → Sort*} {P Q : α} (h : P = Q) {z w : F P}
    (hzw : h ▸ z = h ▸ w) : z = w := by cases h; exact hzw

/-- Two-slot transport of a spectral-sequence product along equalities of bidegrees. -/
theorem mul_transport2 (S : Work.Pi6.CohSS 𝕜) {r : ℕ} {a a' b b' c c' : ℤ × ℤ}
    (ha : a = a') (hb : b = b') (hc : c = c') (h : a + b = c) (h' : a' + b' = c')
    (x : S.E r a) (y : S.E r b) :
    hc ▸ ((S.mul r a b c h x) y) = (S.mul r a' b' c' h' (ha ▸ x)) (hb ▸ y) := by
  cases ha; cases hb; cases hc; rfl

/-! ## The page-2 statement for all elements, from the pure-tensor multiplicativity clause -/

theorem pageTwo_std {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (N : ℕ) (S : Work.Pi6.CohSS (ZMod 2)) (hS : Work.Pi6.IsSerreMSS S p e₀ N)
    (hpage : ∀ (s q s' q' : ℕ) (hs : s + s' ≤ N) (hq : q + q' ≤ N)
      (b : Work.Pi6.Coh (ZMod 2) B s) (f : Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) q)
      (b' : Work.Pi6.Coh (ZMod 2) B s') (f' : Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) q'),
      S.mul 2 ((s : ℤ), (q : ℤ)) ((s' : ℤ), (q' : ℤ)) (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ))
        (by ext <;> simp)
        ((Classical.choose hS s q (by omega) (by omega)).inv.hom (b ⊗ₜ f))
        ((Classical.choose hS s' q' (by omega) (by omega)).inv.hom (b' ⊗ₜ f')) =
      S.mul 2 ((s' : ℤ), (q' : ℤ)) ((s : ℤ), (q : ℤ)) (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ))
        (by ext <;> simp [add_comm])
        ((Classical.choose hS s' q' (by omega) (by omega)).inv.hom (b' ⊗ₜ f'))
        ((Classical.choose hS s q (by omega) (by omega)).inv.hom (b ⊗ₜ f)))
    (s q s' q' : ℕ) (hs : s + s' ≤ N) (hq : q + q' ≤ N)
    (x : S.E 2 ((s : ℤ), (q : ℤ))) (y : S.E 2 ((s' : ℤ), (q' : ℤ))) :
    S.mul 2 ((s : ℤ), (q : ℤ)) ((s' : ℤ), (q' : ℤ)) (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ))
        (by ext <;> simp) x y =
      S.mul 2 ((s' : ℤ), (q' : ℤ)) ((s : ℤ), (q : ℤ)) (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ))
        (by ext <;> simp [add_comm]) y x := by
  let Φ : S.E 2 ((s : ℤ), (q : ℤ)) →ₗ[ZMod 2] S.E 2 ((s' : ℤ), (q' : ℤ)) →ₗ[ZMod 2]
      S.E 2 (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ)) :=
    S.mul 2 ((s : ℤ), (q : ℤ)) ((s' : ℤ), (q' : ℤ)) (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ))
        (by ext <;> simp) -
      (S.mul 2 ((s' : ℤ), (q' : ℤ)) ((s : ℤ), (q : ℤ)) (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ))
        (by ext <;> simp [add_comm])).flip
  have hΦ : Φ = 0 := by
    refine bilin_eq_zero_of_pure
      (X := Work.Pi6.Coh (ZMod 2) B s) (Y := Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) q)
      (X' := Work.Pi6.Coh (ZMod 2) B s') (Y' := Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) q')
      (Classical.choose hS s q (by omega) (by omega)).toLinearEquiv
      (Classical.choose hS s' q' (by omega) (by omega)).toLinearEquiv Φ ?_
    intro b f b' f'
    have hp := hpage s q s' q' hs hq b f b' f'
    simp only [Φ, LinearMap.sub_apply, LinearMap.flip_apply]
    rw [sub_eq_zero]
    exact hp
  have h0 : Φ x y = 0 := by rw [hΦ]; rfl
  exact sub_eq_zero.mp h0

/-! ## Normalisation: from the standard presentation to an arbitrary nonneg triple -/

theorem pageTwo_general {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (N : ℕ) (S : Work.Pi6.CohSS (ZMod 2)) (hS : Work.Pi6.IsSerreMSS S p e₀ N)
    (hstd : ∀ (s q s' q' : ℕ) (hs : s + s' ≤ N) (hq : q + q' ≤ N)
      (x : S.E 2 ((s : ℤ), (q : ℤ))) (y : S.E 2 ((s' : ℤ), (q' : ℤ))),
      S.mul 2 ((s : ℤ), (q : ℤ)) ((s' : ℤ), (q' : ℤ)) (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ))
          (by ext <;> simp) x y =
        S.mul 2 ((s' : ℤ), (q' : ℤ)) ((s : ℤ), (q : ℤ)) (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ))
          (by ext <;> simp [add_comm]) y x)
    (a b c : ℤ × ℤ) (h : a + b = c) (x : S.E 2 a) (y : S.E 2 b)
    (ha1 : 0 ≤ a.1) (ha2 : 0 ≤ a.2) (hb1 : 0 ≤ b.1) (hb2 : 0 ≤ b.2)
    (hN1 : a.1 + b.1 ≤ (N : ℤ)) (hN2 : a.2 + b.2 ≤ (N : ℤ)) :
    S.mul 2 a b c h x y = S.mul 2 b a c (by rw [← h]; abel) y x := by
  set s := a.1.toNat with hsdef
  set q := a.2.toNat with hqdef
  set s' := b.1.toNat with hs'def
  set q' := b.2.toNat with hq'def
  have ha1' : (s : ℤ) = a.1 := by rw [hsdef]; exact Int.toNat_of_nonneg ha1
  have ha2' : (q : ℤ) = a.2 := by rw [hqdef]; exact Int.toNat_of_nonneg ha2
  have hb1' : (s' : ℤ) = b.1 := by rw [hs'def]; exact Int.toNat_of_nonneg hb1
  have hb2' : (q' : ℤ) = b.2 := by rw [hq'def]; exact Int.toNat_of_nonneg hb2
  have hs : s + s' ≤ N := by omega
  have hq : q + q' ≤ N := by omega
  have ha : a = ((s : ℤ), (q : ℤ)) := by ext <;> simp [ha1', ha2']
  have hb : b = ((s' : ℤ), (q' : ℤ)) := by ext <;> simp [hb1', hb2']
  have hc : c = (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ)) := by
    rw [← h]
    ext <;> simp [ha, hb]
  have hT : ((s : ℤ), (q : ℤ)) + ((s' : ℤ), (q' : ℤ)) =
      (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ)) := rfl
  have hBs : ((s' : ℤ), (q' : ℤ)) + ((s : ℤ), (q : ℤ)) =
      (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ)) := by ext <;> simp [add_comm]
  have e1 : hc ▸ (S.mul 2 a b c h x y) =
      S.mul 2 ((s : ℤ), (q : ℤ)) ((s' : ℤ), (q' : ℤ))
        (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ)) hT (ha ▸ x) (hb ▸ y) :=
    mul_transport2 S ha hb hc h hT x y
  have e2 : hc ▸ (S.mul 2 b a c (by rw [← h]; abel) y x) =
      S.mul 2 ((s' : ℤ), (q' : ℤ)) ((s : ℤ), (q : ℤ))
        (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ)) hBs (hb ▸ y) (ha ▸ x) :=
    mul_transport2 S hb ha hc (by rw [← h]; abel) hBs y x
  have key := hstd s q s' q' hs hq (ha ▸ x) (hb ▸ y)
  rw [S.mul_congr 2 ((s : ℤ), (q : ℤ)) ((s' : ℤ), (q' : ℤ)) _ hT (by ext <;> simp)
      (ha ▸ x) (hb ▸ y)] at key
  rw [S.mul_congr 2 ((s' : ℤ), (q' : ℤ)) ((s : ℤ), (q : ℤ)) _ hBs (by ext <;> simp [add_comm])
      (hb ▸ y) (ha ▸ x)] at key
  refine eqRec_inj (F := fun P => ↑(S.E 2 P)) hc ?_
  rw [e1, e2]
  exact key


/-! ## The two delegated ingredients, as hypotheses: the assembly -/

/-- **Assembly.**  Page-two commutativity for pure tensors (the multiplicativity clause), together
with the propagation of commutativity along the pages, implies `Work.Pi6.EMM2.mulComm`. -/
theorem mulComm_of_pieces {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : ContinuousMap E B) (e₀ : E) (N : ℕ) (S : Work.Pi6.CohSS (ZMod 2))
    (hS : Work.Pi6.IsSerreMSS S p e₀ N)
    (hpage : ∀ (s q s' q' : ℕ) (hs : s + s' ≤ N) (hq : q + q' ≤ N)
      (b : Work.Pi6.Coh (ZMod 2) B s) (f : Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) q)
      (b' : Work.Pi6.Coh (ZMod 2) B s') (f' : Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) q'),
      S.mul 2 ((s : ℤ), (q : ℤ)) ((s' : ℤ), (q' : ℤ)) (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ))
        (by ext <;> simp)
        ((Classical.choose hS s q (by omega) (by omega)).inv.hom (b ⊗ₜ f))
        ((Classical.choose hS s' q' (by omega) (by omega)).inv.hom (b' ⊗ₜ f')) =
      S.mul 2 ((s' : ℤ), (q' : ℤ)) ((s : ℤ), (q : ℤ)) (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ))
        (by ext <;> simp [add_comm])
        ((Classical.choose hS s' q' (by omega) (by omega)).inv.hom (b' ⊗ₜ f'))
        ((Classical.choose hS s q (by omega) (by omega)).inv.hom (b ⊗ₜ f)))
    :
    ∀ (r : ℕ) (a b c : ℤ × ℤ) (h : a + b = c) (x : S.E r a) (y : S.E r b), 2 ≤ r →
      0 ≤ a.1 → 0 ≤ a.2 → 0 ≤ b.1 → 0 ≤ b.2 → a.1 + b.1 ≤ (N : ℤ) → a.2 + b.2 ≤ (N : ℤ) →
      S.mul r a b c h x y = S.mul r b a c (by rw [← h]; abel) y x := by
  intro r a b c h x y hr ha1 ha2 hb1 hb2 hN1 hN2
  exact mulCommPropagation (ZMod 2) S a b c h
    (fun u v => pageTwo_general p e₀ N S hS (pageTwo_std p e₀ N S hS hpage)
      a b c h u v ha1 ha2 hb1 hb2 hN1 hN2) r x y hr

theorem mulComm {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : ContinuousMap E B)
    (e₀ : E) (N : ℕ) (S : Work.Pi6.CohSS (ZMod 2)) (hS : Work.Pi6.IsSerreMSS S p e₀ N) :
    ∀ (r : ℕ) (a b c : ℤ × ℤ) (h : a + b = c) (x : S.E r a) (y : S.E r b), 2 ≤ r →
      0 ≤ a.1 → 0 ≤ a.2 → 0 ≤ b.1 → 0 ≤ b.2 → a.1 + b.1 ≤ (N : ℤ) → a.2 + b.2 ≤ (N : ℤ) →
      S.mul r a b c h x y = S.mul r b a c (by rw [← h]; abel) y x := by
  intro r a b c h x y hr ha1 ha2 hb1 hb2 hN1 hN2
  exact mulComm_of_pieces p e₀ N S hS (mulCommPageTwo p e₀ N S hS)
    r a b c h x y hr ha1 ha2 hb1 hb2 hN1 hN2

end Work.Pi6.EMM2
