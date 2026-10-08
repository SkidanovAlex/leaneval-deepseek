import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.AppXIField.L0.exists_sigma_of_iota`

Appendix XI Prop. 2, second half: the `B`-action by field automorphisms.

Let `V` be a finite additive group, `A` a finite abelian group acting on `V`, and `B` a group
acting on `V` in a `φ`-semilinear way (`hcompat`: `b • (a • v) = (φ b a) • (b • v)`).
Suppose `V` is additively isomorphic to a finite field `K` through `e : V ≃+ K`, that the
`A`-action becomes multiplication by the values of `ι : A →* Kˣ`
(`hA : e (a • v) = (ι a) * e v`), and that `ι(A)` generates `K` as a ring (`hgen`).

Then `B` acts on `K` through a monoid hom `σ : B →* (K ≃+* K)` into the field automorphisms,
compatible with `φ`: `σ b (ι a) = ι (φ b a)`.

## Proof sketch

For `b : B` the map `F_b k := e (b • e.symm k)` is additive (it is the transport of the additive
automorphism `v ↦ b • v` of `V` along `e`).  It is *not* multiplicative, but it is
"multiplicative on the generators up to a scalar": for `a : A`, `y : K`

* `F_b ((ι a) * y) = (ι (φ b a)) * F_b y`,  and
* `F_b (ι a) = (ι (φ b a)) * F_b 1`,

both being immediate rewritings with `hA`, `hcompat` and the inverse form of `hA`.
Hence after normalising with `c_b := F_b 1 ≠ 0` the map `σ_b k := F_b k / c_b` is additive,
`σ_b 1 = 1`, sends `ι a` to `ι (φ b a)`, and satisfies
`σ_b ((ι a) * y) = σ_b (ι a) * σ_b y`.

The multiplicativity of `σ_b` everywhere then follows from `hgen`: for fixed `y` the set
`U = {z | σ_b (z * y) = σ_b z * σ_b y}` is an additive subgroup closed under left multiplication
by every element of `ι(A)`; the set of such left multipliers is a subring, hence contains the
`Subring.closure` of `ι(A)`, which is everything; `U` is therefore a nonzero ideal of the field
`K` and equals `K`.  (`mul_eq_of_generating` packages this.)

As `σ_b` is an additive bijection it is a field automorphism (`RingEquiv.ofBijective`).  Finally
`σ_1 = 1` and `σ_{b₁ b₂} = σ_{b₁} ∘ σ_{b₂}` hold because both sides are field automorphisms
agreeing on the generating set `ι(A)` (`ringEquiv_ext_closure`).
-/

set_option autoImplicit false

namespace Work.AppXIField.L0

noncomputable section

/-! ## Elementary re-usable lemmas -/

/-- The additive equivalence `V ≃+ V` given by the action of `b : B` (inverse: the action
of `b⁻¹`). -/
def smulAddEquiv {B V : Type*} [Group B] [AddCommGroup V] [DistribMulAction B V] (b : B) :
    V ≃+ V where
  toFun v := b • v
  invFun v := b⁻¹ • v
  left_inv v := by
    change b⁻¹ • (b • v) = v
    rw [← mul_smul, inv_mul_cancel, one_smul]
  right_inv v := by
    change b • (b⁻¹ • v) = v
    rw [← mul_smul, mul_inv_cancel, one_smul]
  map_add' x y := smul_add b x y

@[simp] theorem smulAddEquiv_apply {B V : Type*} [Group B] [AddCommGroup V]
    [DistribMulAction B V] (b : B) (v : V) : smulAddEquiv b v = b • v := rfl

/-- Right multiplication by a fixed nonzero `d` as an additive equivalence of a division ring. -/
def mulRightAddEquiv {K : Type*} [DivisionRing K] (d : K) (hd : d ≠ 0) : K ≃+ K where
  toFun k := k * d
  invFun k := k * d⁻¹
  left_inv k := by
    change (k * d) * d⁻¹ = k
    rw [mul_assoc, mul_inv_cancel₀ hd, mul_one]
  right_inv k := by
    change (k * d⁻¹) * d = k
    rw [mul_assoc, inv_mul_cancel₀ hd, mul_one]
  map_add' x y := add_mul x y d

@[simp] theorem mulRightAddEquiv_apply {K : Type*} [DivisionRing K] (d : K) (hd : d ≠ 0)
    (k : K) : mulRightAddEquiv d hd k = k * d := rfl

/-- **A generator criterion for multiplicativity.**  An additive map `f : K → K` on a field that
is multiplicative for multiplication on the left by every element of a set `s` (containing a
nonzero element) whose `Subring.closure` is all of `K`, is multiplicative everywhere. -/
theorem mul_eq_of_generating {K : Type*} [Field K] (f : K → K)
    (hadd : ∀ x y : K, f (x + y) = f x + f y)
    {s : Set K} (hs : Subring.closure s = ⊤) (hsne : ∃ z ∈ s, z ≠ 0)
    (hbase : ∀ x ∈ s, ∀ y : K, f (x * y) = f x * f y) :
    ∀ x y : K, f (x * y) = f x * f y := by
  have hf0 : f 0 = 0 := by
    have h : f (0 + 0) = f 0 + f 0 := hadd 0 0
    rw [add_zero] at h
    have h2 : f 0 + 0 = f 0 + f 0 := by rw [add_zero]; exact h
    exact (add_left_cancel h2).symm
  have hneg : ∀ x : K, f (-x) = -f x := by
    intro x
    have h := hadd x (-x)
    rw [add_neg_cancel, hf0] at h
    rw [eq_comm] at h
    exact eq_neg_of_add_eq_zero_right h
  intro x y
  set U : Set K := {z | f (z * y) = f z * f y} with hU
  have hUadd : ∀ a b, a ∈ U → b ∈ U → a + b ∈ U := by
    intro a b ha hb
    simp only [hU, Set.mem_ofPred_eq] at ha hb ⊢
    rw [add_mul, hadd, ha, hb, hadd a b, add_mul]
  have hUneg : ∀ a, a ∈ U → -a ∈ U := by
    intro a ha
    simp only [hU, Set.mem_ofPred_eq] at ha ⊢
    rw [neg_mul, hneg, ha, hneg, neg_mul]
  have hsub : s ⊆ U := by
    intro z hz
    simp only [hU, Set.mem_ofPred_eq]
    exact hbase z hz y
  let T : Subring K :=
    { carrier := {t | ∀ z, z ∈ U → t * z ∈ U}
      zero_mem' := by
        intro z hz
        rw [zero_mul]
        simp only [hU, Set.mem_ofPred_eq]
        rw [zero_mul, hf0, zero_mul]
      one_mem' := by intro z hz; simpa using hz
      add_mem' := by
        intro a b ha hb z hz
        rw [add_mul]
        exact hUadd _ _ (ha z hz) (hb z hz)
      neg_mem' := by
        intro a ha z hz
        rw [neg_mul]
        exact hUneg _ (ha z hz)
      mul_mem' := by
        intro a b ha hb z hz
        rw [mul_assoc]
        exact ha _ (hb z hz) }
  have hsT : s ⊆ (T : Set K) := by
    intro z hz w hw
    simp only [hU, Set.mem_ofPred_eq] at hw ⊢
    rw [mul_assoc, hbase z hz (w * y), hw, hbase z hz w, mul_assoc]
  have hT : Subring.closure s ≤ T := Subring.closure_le.mpr hsT
  have hmemT : ∀ t : K, t ∈ T := fun t => hT (by rw [hs]; trivial)
  obtain ⟨z0, hz0s, hz0ne⟩ := hsne
  have hz0U : z0 ∈ U := hsub hz0s
  have hu : x ∈ U := by
    have := hmemT (x * z0⁻¹) z0 hz0U
    rwa [mul_assoc, inv_mul_cancel₀ hz0ne, mul_one] at this
  simpa only [hU, Set.mem_ofPred_eq] using hu

/-- **Extensionality of ring equivalences from a generating set.** -/
theorem ringEquiv_ext_closure {K : Type*} [Ring K] (f g : K ≃+* K) {s : Set K}
    (hs : Subring.closure s = ⊤) (h : ∀ x ∈ s, f x = g x) : f = g := by
  ext x
  have hx : x ∈ Subring.closure s := by rw [hs]; trivial
  induction hx using Subring.closure_induction with
  | mem y hy => exact h y hy
  | zero => simp
  | one => simp
  | add y z hy hz ihy ihz => simp [map_add, ihy, ihz]
  | neg y hy ihy => simp [ihy]
  | mul y z hy hz ihy ihz => simp [map_mul, ihy, ihz]

/-! ## The target -/

theorem exists_sigma_of_iota {V A B K : Type} [AddCommGroup V] [Finite V] [CommGroup A] [Finite A]
    [Group B] [DistribMulAction A V] [DistribMulAction B V] [Field K] [Fintype K]
    (φ : B →* MulAut A)
    (hcompat : ∀ (b : B) (a : A) (v : V), b • (a • v) = (φ b a) • (b • v))
    (e : V ≃+ K) (ι : A →* Kˣ)
    (hA : ∀ (a : A) (v : V), e (a • v) = (ι a : K) * e v)
    (hgen : Subring.closure (Set.range fun a : A => (ι a : K)) = ⊤) :
    ∃ σ : B →* (K ≃+* K), ∀ (b : B) (a : A), σ b (ι a : K) = (ι (φ b a) : K) := by
  classical
  -- `ι(A)` contains a nonzero element (all its values are units).
  have hsne : ∃ z ∈ Set.range fun a : A => (ι a : K), z ≠ 0 :=
    ⟨(ι 1 : K), ⟨1, rfl⟩, Units.ne_zero (ι 1)⟩
  -- The additive automorphism of `K` induced by `b`: `k ↦ e (b • e.symm k)`.
  let A_b : B → (K ≃+ K) := fun b => (e.symm.trans (smulAddEquiv b)).trans e
  have hA_b : ∀ b k, A_b b k = e (b • e.symm k) := by
    intro b k
    simp only [A_b, AddEquiv.trans_apply, smulAddEquiv_apply]
  -- The normalising scalar `c_b := A_b b 1`.
  let cst : B → K := fun b => A_b b 1
  have hcst_ne : ∀ b, cst b ≠ 0 := by
    intro b h
    exact one_ne_zero ((A_b b).injective (by rw [map_zero]; exact h))
  -- The normalised map `σ_b k = A_b b k / c_b`.
  let sig : B → (K ≃+ K) :=
    fun b => (A_b b).trans (mulRightAddEquiv (cst b)⁻¹ (inv_ne_zero (hcst_ne b)))
  have hsig_apply : ∀ b k, sig b k = A_b b k * (cst b)⁻¹ := by
    intro b k
    simp only [sig, AddEquiv.trans_apply, mulRightAddEquiv_apply]
  -- The inverse form of `hA`.
  have he_symm_mul : ∀ (a : A) (k : K), e.symm ((ι a : K) * k) = a • e.symm k := by
    intro a k
    apply e.injective
    rw [e.apply_symm_apply, hA a (e.symm k), e.apply_symm_apply]
  -- Multiplicativity of `A_b` on the generators, up to the scalar `c_b`.
  have hFbase : ∀ (b : B) (a : A) (y : K),
      A_b b ((ι a : K) * y) = (ι (φ b a) : K) * A_b b y := by
    intro b a y
    rw [hA_b b ((ι a) * y), he_symm_mul a y, hcompat b a (e.symm y), hA_b b y,
        hA (φ b a) (b • e.symm y)]
  have hFgen : ∀ (b : B) (a : A), A_b b (ι a : K) = (ι (φ b a) : K) * cst b := by
    intro b a
    have h1 := hFbase b a 1
    rw [mul_one] at h1
    exact h1
  -- The values of `σ_b` on the generators.
  have hsig_gen : ∀ (b : B) (a : A), sig b (ι a : K) = (ι (φ b a) : K) := by
    intro b a
    rw [hsig_apply, hFgen b a, mul_assoc, mul_inv_cancel₀ (hcst_ne b), mul_one]
  have hsig_one : ∀ b, sig b 1 = 1 := by
    intro b
    rw [hsig_apply]
    show cst b * (cst b)⁻¹ = 1
    rw [mul_inv_cancel₀ (hcst_ne b)]
  -- Multiplicativity of `σ_b` on the generators.
  have hsig_mul_base : ∀ (b : B) (a : A) (y : K),
      sig b ((ι a : K) * y) = sig b (ι a : K) * sig b y := by
    intro b a y
    rw [hsig_apply, hsig_apply, hsig_apply, hFbase b a y, hFgen b a]
    rw [mul_assoc ((ι (φ b a) : K)) (cst b) ((cst b)⁻¹), mul_inv_cancel₀ (hcst_ne b),
        mul_one, mul_assoc]
  -- Multiplicativity everywhere, from `hgen` (`ι(A)` generates `K` as a ring).
  have hsig_mul : ∀ b, ∀ x y : K, sig b (x * y) = sig b x * sig b y := fun b =>
    mul_eq_of_generating (fun k => sig b k) (fun x y => (sig b).map_add x y) hgen hsne
      (fun x hx y => by obtain ⟨a, rfl⟩ := hx; exact hsig_mul_base b a y)
  -- Package `σ_b` as a ring homomorphism, then as a field automorphism.
  let ring : B → (K →+* K) := fun b =>
    { toFun := sig b
      map_one' := hsig_one b
      map_mul' := hsig_mul b
      map_zero' := (sig b).map_zero
      map_add' := (sig b).map_add }
  let sb : B → (K ≃+* K) := fun b => RingEquiv.ofBijective (ring b) (sig b).bijective
  have hsb : ∀ b k, sb b k = sig b k := fun b k => rfl
  refine ⟨{ toFun := sb
            map_one' := ?_
            map_mul' := ?_ }, ?_⟩
  · -- `σ_1 = 1`
    apply ringEquiv_ext_closure _ _ hgen
    intro x hx
    obtain ⟨a, rfl⟩ := hx
    show sig 1 (ι a) = (1 : K ≃+* K) (ι a)
    rw [hsig_gen 1 a]
    simp
  · -- `σ_{b₁ b₂} = σ_{b₁} ∘ σ_{b₂}`
    intro b1 b2
    apply ringEquiv_ext_closure _ _ hgen
    intro x hx
    obtain ⟨a, rfl⟩ := hx
    show sig (b1 * b2) (ι a) = (sb b1 * sb b2) (ι a)
    rw [show (sb b1 * sb b2) (ι a) = sb b1 (sb b2 (ι a)) from rfl,
        hsb b1 (sb b2 (ι a)), hsb b2 (ι a),
        hsig_gen b2 a, hsig_gen b1 (φ b2 a), hsig_gen (b1 * b2) a, map_mul]
    rfl
  · -- compatibility with `φ`
    intro b a
    show sig b (ι a) = (ι (φ b a) : K)
    exact hsig_gen b a

end

end Work.AppXIField.L0
