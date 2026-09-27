import Mathlib
import Submission.Work.KT.Defs

/-!
# `Work.KT.ExtGen.Basic` — support definitions for the node `ext_generator`

Auxiliary notions used to state the pieces `ext_generator` is assembled from:

* `R2` — the standard two-dimensional real normed space `ℝ × ℝ` (maximum norm), the factor by
  which the suspension lemma suspends.
* `augPair_eq_of_mem_bdry` / `mapA_augPair_apply_eq_of_mem_bdry` — on `Kpair V`, evaluation at any
  two boundary points is the same character; hence the reduced subgroup `K̃(Kpair V)` does not
  depend on the base point.
* `exists_eq_smul_eq_one_or_neg_one` — two generators of the same reduced subgroup, one of which
  has infinite order, differ by `±1`.
* `pairIso` — an isomorphism of the pair structure
  `(Kpair V, Kpair W, Kpair (V × W), prodAlg V W)` transported to `(V', W')`.  This is the data
  along which the *statement* of `ext_generator` transports (see `ext_generator_transport`), and it
  is produced geometrically in `ExtGen/Transport`.
* `pairAssocEquiv` — the canonical algebra isomorphism
  `Kpair ((V × W) × Z) ≃ₐ[ℂ] Kpair (V × (W × Z))` induced by associativity of the product of
  normed spaces (the maximum norm is associative).  It is the "canonical ring isomorphism" up to
  which associativity of the external product is formulated in `ExtGen/Nesting`.
-/

set_option linter.unusedSimpArgs false

namespace Work.KT

noncomputable section

/-- The standard two-dimensional real normed space (the maximum norm on `ℝ × ℝ`), the factor
by which the suspension lemma suspends. -/
abbrev R2 : Type := ℝ × ℝ

/-- The standard `n`-dimensional real normed space (the sup norm on `Fin n → ℝ`). -/
abbrev Std (n : ℕ) : Type := Fin n → ℝ

/-! ## Base point independence of the reduced group -/

/-- On `Kpair V` (functions on the ball constant on the boundary sphere) evaluation at two
boundary points gives the same character. -/
lemma augPair_eq_of_mem_bdry (V : Type) [NormedAddCommGroup V] (y y' : Ball V)
    (hy : y ∈ bdry V) (hy' : y' ∈ bdry V) : augPair V y = augPair V y' := by
  ext F
  show (F : Ball V → ℂ) y = (F : Ball V → ℂ) y'
  exact F.2 y hy y' hy'

/-- The reduced subgroup `K̃(Kpair V)` is independent of the base point (taken on the boundary). -/
lemma mapA_augPair_apply_eq_of_mem_bdry (V : Type) [NormedAddCommGroup V] (y y' : Ball V)
    (hy : y ∈ bdry V) (hy' : y' ∈ bdry V) (z : K0 (Kpair V)) :
    K0.mapA (augPair V y) z = K0.mapA (augPair V y') z := by
  rw [augPair_eq_of_mem_bdry V y y' hy hy']

/-! ## Uniqueness of generators -/

/-- **Uniqueness of generators up to sign.**  If `s` and `g` both generate the same reduced
subgroup and `g` has infinite order, then `s = ± g`. -/
lemma exists_eq_smul_eq_one_or_neg_one {A : Type} [Ring A] (f : K0 A →+ ℤ) (s g : K0 A)
    (hs : f s = 0) (hg : f g = 0)
    (hgs : ∀ z, f z = 0 → ∃ n : ℤ, z = n • g)
    (hsg : ∀ z, f z = 0 → ∃ n : ℤ, z = n • s)
    (hinf : ∀ k : ℤ, k • g = 0 → k = 0) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ s = ε • g := by
  obtain ⟨m, hm⟩ := hgs s hs
  obtain ⟨n, hn⟩ := hsg g hg
  have h2 : g = (n * m) • g := by
    calc g = n • s := hn
      _ = n • (m • g) := by rw [hm]
      _ = (n * m) • g := by rw [smul_smul]
  have h1 : (n * m - 1) • g = 0 := by
    rw [sub_smul, one_smul, ← h2, sub_self]
  have h2 : n * m - 1 = 0 := hinf _ h1
  have h3 : m * n = 1 := by rw [mul_comm]; omega
  exact ⟨m, Int.eq_one_or_neg_one_of_mul_eq_one h3, hm⟩

/-! ## Isomorphisms of the pair structure -/

/-- The pair structure of `(V, W)` transported to `(V', W')`: algebra isomorphisms of the four
function algebras, compatible with the pullbacks `pullFst`, `pullSnd` and the smash inclusion, and
transporting boundary augmentations of each of the three function algebras. -/
structure pairIso (V W V' W' : Type) [NormedAddCommGroup V] [NormedAddCommGroup W]
    [NormedAddCommGroup V'] [NormedAddCommGroup W'] where
  /-- the isomorphism `Kpair V ≃ₐ Kpair V'` -/
  EV : Kpair V ≃ₐ[ℂ] Kpair V'
  /-- the isomorphism `Kpair W ≃ₐ Kpair W'` -/
  EW : Kpair W ≃ₐ[ℂ] Kpair W'
  /-- the isomorphism `Kpair (V × W) ≃ₐ Kpair (V' × W')` -/
  EPi : Kpair (V × W) ≃ₐ[ℂ] Kpair (V' × W')
  /-- the isomorphism `prodAlg V W ≃ₐ prodAlg V' W'` -/
  Phi : prodAlg V W ≃ₐ[ℂ] prodAlg V' W'
  /-- compatibility with `pullFst` -/
  hfst : Phi.toAlgHom.comp (pullFst V W) = (pullFst V' W').comp EV.toAlgHom
  /-- compatibility with `pullSnd` -/
  hsnd : Phi.toAlgHom.comp (pullSnd V W) = (pullSnd V' W').comp EW.toAlgHom
  /-- compatibility with the smash inclusion -/
  hsm : Phi.toAlgHom.comp (smashIncl V W) = (smashIncl V' W').comp EPi.toAlgHom
  /-- every boundary augmentation of `Kpair V'` is the transport of a boundary augmentation of
  `Kpair V` -/
  hV : ∀ y' : Ball V', y' ∈ bdry V' →
    ∃ y : Ball V, y ∈ bdry V ∧ (augPair V' y').comp EV.toAlgHom = augPair V y
  /-- every boundary augmentation of `Kpair W'` is the transport of a boundary augmentation of
  `Kpair W` -/
  hW : ∀ y' : Ball W', y' ∈ bdry W' →
    ∃ y : Ball W, y ∈ bdry W ∧ (augPair W' y').comp EW.toAlgHom = augPair W y
  /-- every boundary augmentation of `Kpair (V' × W')` is the transport of a boundary augmentation
  of `Kpair (V × W)` -/
  hPi : ∀ y' : Ball (V' × W'), y' ∈ bdry (V' × W') →
    ∃ y : Ball (V × W), y ∈ bdry (V × W) ∧
      (augPair (V' × W') y').comp EPi.toAlgHom = augPair (V × W) y

/-! ## Associativity of the product of balls -/

/-- The canonical map `D_{V × (W × Z)} = D_V × D_W × D_Z → D_{(V × W) × Z}`; it is the identity on
the underlying points, transported across associativity of products. -/
def ballAssoc (V W Z : Type) [NormedAddCommGroup V] [NormedAddCommGroup W]
    [NormedAddCommGroup Z] : C(Ball (V × (W × Z)), Ball ((V × W) × Z)) :=
  ⟨fun z => ⟨(((z : V × (W × Z)).1, (z : V × (W × Z)).2.1), (z : V × (W × Z)).2.2), by
      have hz : max ‖(z : V × (W × Z)).1‖
          (max ‖(z : V × (W × Z)).2.1‖ ‖(z : V × (W × Z)).2.2‖) ≤ 1 := by
        have h := Metric.mem_closedBall.mp z.2
        rw [dist_eq_norm, sub_zero, Prod.norm_def] at h
        exact h
      have h1 : ‖(z : V × (W × Z)).1‖ ≤ 1 := (max_le_iff.mp hz).1
      have h2 : ‖(z : V × (W × Z)).2.1‖ ≤ 1 := (max_le_iff.mp (max_le_iff.mp hz).2).1
      have h3 : ‖(z : V × (W × Z)).2.2‖ ≤ 1 := (max_le_iff.mp (max_le_iff.mp hz).2).2
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Prod.norm_def]
      exact max_le (max_le h1 h2) h3⟩, by fun_prop⟩

/-- The inverse of `ballAssoc`. -/
def ballAssocInv (V W Z : Type) [NormedAddCommGroup V] [NormedAddCommGroup W]
    [NormedAddCommGroup Z] : C(Ball ((V × W) × Z), Ball (V × (W × Z))) :=
  ⟨fun z => ⟨((z : (V × W) × Z).1.1, ((z : (V × W) × Z).1.2, (z : (V × W) × Z).2)), by
      have hz : max (max ‖(z : (V × W) × Z).1.1‖ ‖(z : (V × W) × Z).1.2‖)
          ‖(z : (V × W) × Z).2‖ ≤ 1 := by
        have h := Metric.mem_closedBall.mp z.2
        rw [dist_eq_norm, sub_zero, Prod.norm_def] at h
        exact h
      have h1 : ‖(z : (V × W) × Z).1.1‖ ≤ 1 := (max_le_iff.mp (max_le_iff.mp hz).1).1
      have h2 : ‖(z : (V × W) × Z).1.2‖ ≤ 1 := (max_le_iff.mp (max_le_iff.mp hz).1).2
      have h3 : ‖(z : (V × W) × Z).2‖ ≤ 1 := (max_le_iff.mp hz).2
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Prod.norm_def]
      exact max_le h1 (max_le h2 h3)⟩, by fun_prop⟩

/-- `ballAssoc` preserves the norm. -/
lemma norm_ballAssoc (V W Z : Type) [NormedAddCommGroup V] [NormedAddCommGroup W]
    [NormedAddCommGroup Z] (z : Ball (V × (W × Z))) :
    ‖((ballAssoc V W Z z : Ball ((V × W) × Z)) : (V × W) × Z)‖ =
      ‖(z : V × (W × Z))‖ := by
  simp only [ballAssoc, ContinuousMap.coe_mk, Prod.norm_def]
  rw [max_assoc]

/-- `ballAssocInv` preserves the norm. -/
lemma norm_ballAssocInv (V W Z : Type) [NormedAddCommGroup V] [NormedAddCommGroup W]
    [NormedAddCommGroup Z] (z : Ball ((V × W) × Z)) :
    ‖((ballAssocInv V W Z z : Ball (V × (W × Z))) : V × (W × Z))‖ =
      ‖(z : (V × W) × Z)‖ := by
  simp only [ballAssocInv, ContinuousMap.coe_mk, Prod.norm_def]
  rw [max_assoc]

/-- `ballAssocInv` is a left inverse of `ballAssoc`. -/
lemma ballAssocInv_ballAssoc (V W Z : Type) [NormedAddCommGroup V] [NormedAddCommGroup W]
    [NormedAddCommGroup Z] (z : Ball (V × (W × Z))) :
    ballAssocInv V W Z (ballAssoc V W Z z) = z := by
  apply Subtype.ext
  obtain ⟨⟨v, w, zz⟩, hz⟩ := z
  rfl

/-- `ballAssocInv` is a right inverse of `ballAssoc`. -/
lemma ballAssoc_ballAssocInv (V W Z : Type) [NormedAddCommGroup V] [NormedAddCommGroup W]
    [NormedAddCommGroup Z] (z : Ball ((V × W) × Z)) :
    ballAssoc V W Z (ballAssocInv V W Z z) = z := by
  apply Subtype.ext
  obtain ⟨⟨v, w⟩, zz⟩ := z
  rfl

/-- Associativity of the product of balls, as a homeomorphism. -/
def ballAssocHomeo (V W Z : Type) [NormedAddCommGroup V] [NormedAddCommGroup W]
    [NormedAddCommGroup Z] : Ball (V × (W × Z)) ≃ₜ Ball ((V × W) × Z) where
  toFun := ballAssoc V W Z
  invFun := ballAssocInv V W Z
  left_inv := ballAssocInv_ballAssoc V W Z
  right_inv := ballAssoc_ballAssocInv V W Z
  continuous_toFun := (ballAssoc V W Z).continuous
  continuous_invFun := (ballAssocInv V W Z).continuous

/-! ## Pullback of `Kpair` along a homeomorphism of ball pairs -/

/-- Pullback of `Kpair` along a pair of mutually inverse continuous maps of ball pairs which
preserve the boundary: the algebra isomorphism `Kpair U ≃ₐ[ℂ] Kpair U'` given by
`F ↦ F ∘ f`.  (Taking `f = φ.symm` for a homeomorphism `φ` of ball pairs, this is the transport
of the pair structure along a norm change.) -/
def pairPullbackEquiv {U U' : Type} [NormedAddCommGroup U] [NormedAddCommGroup U']
    (f : C(Ball U', Ball U)) (g : C(Ball U, Ball U'))
    (hfg : ∀ y : Ball U', g (f y) = y) (hgf : ∀ x : Ball U, f (g x) = x)
    (h1 : ∀ y : Ball U', y ∈ bdry U' → f y ∈ bdry U)
    (h2 : ∀ x : Ball U, x ∈ bdry U → g x ∈ bdry U') :
    Kpair U ≃ₐ[ℂ] Kpair U' :=
  AlgEquiv.ofAlgHom
    (AlgHom.codRestrict ((ContinuousMap.compStarAlgHom' ℂ ℂ f).toAlgHom.comp (Kpair U).val)
      (Kpair U') (by
        intro F y hy y' hy'
        exact F.2 (f y) (h1 y hy) (f y') (h1 y' hy')))
    (AlgHom.codRestrict ((ContinuousMap.compStarAlgHom' ℂ ℂ g).toAlgHom.comp (Kpair U').val)
      (Kpair U) (by
        intro F x hx x' hx'
        exact F.2 (g x) (h2 x hx) (g x') (h2 x' hx')))
    (by
      apply AlgHom.ext
      intro F
      apply Subtype.ext
      apply ContinuousMap.ext
      intro y
      simp only [AlgHom.comp_apply, AlgHom.coe_id, id_eq, AlgHom.coe_comp,
        ContinuousMap.compStarAlgHom'_apply, StarAlgHom.coe_toAlgHom, AlgHom.coe_codRestrict,
        ContinuousMap.comp_apply, ContinuousMap.coe_mk, Subalgebra.coe_val, Function.comp_apply]
      exact congrArg (fun z => (F : Ball U' → ℂ) z) (hfg y))
    (by
      apply AlgHom.ext
      intro F
      apply Subtype.ext
      apply ContinuousMap.ext
      intro x
      simp only [AlgHom.comp_apply, AlgHom.coe_id, id_eq, AlgHom.coe_comp,
        ContinuousMap.compStarAlgHom'_apply, StarAlgHom.coe_toAlgHom, AlgHom.coe_codRestrict,
        ContinuousMap.comp_apply, ContinuousMap.coe_mk, Subalgebra.coe_val, Function.comp_apply]
      exact congrArg (fun z => (F : Ball U → ℂ) z) (hgf x))

/-- **The canonical algebra isomorphism `Kpair ((V × W) × Z) ≃ₐ[ℂ] Kpair (V × (W × Z))`**
induced by associativity of the (maximum) norm on products. -/
def pairAssocEquiv (V W Z : Type) [NormedAddCommGroup V] [NormedAddCommGroup W]
    [NormedAddCommGroup Z] : Kpair ((V × W) × Z) ≃ₐ[ℂ] Kpair (V × (W × Z)) :=
  pairPullbackEquiv (ballAssoc V W Z) (ballAssocInv V W Z)
    (ballAssocInv_ballAssoc V W Z) (ballAssoc_ballAssocInv V W Z)
    (by
      intro y hy
      show ‖((ballAssoc V W Z y : Ball ((V × W) × Z)) : (V × W) × Z)‖ = 1
      rw [norm_ballAssoc]
      exact hy)
    (by
      intro x hx
      show ‖((ballAssocInv V W Z x : Ball (V × (W × Z))) : V × (W × Z))‖ = 1
      rw [norm_ballAssocInv]
      exact hx)

end

end Work.KT
