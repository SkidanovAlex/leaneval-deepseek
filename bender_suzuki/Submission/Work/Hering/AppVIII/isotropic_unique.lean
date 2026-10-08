import Mathlib
import Submission.Work.Hering.AppVIII.PolarDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `W = {u | u.1 = 0}` is the unique totally isotropic `𝔽₂`-subspace of `K × K` of order `8`

For `K = KC 1 = GF(8)` and `ε ≠ 0`, the polar form

  `betaP ε u v = u.1 * v.1² + v.1 * u.1² + ε * (u.1⁴ * v.2⁴ + v.1⁴ * u.2⁴)`

of the squaring map of `C(3,ε)` is `𝔽₂`-bilinear, alternating and non-degenerate, and

  `W = {u : K × K | u.1 = 0}`

is a totally isotropic subspace of order `8`.  Here we prove that it is the *only* one, which
is what forces every automorphism of `C(3,ε)` to stabilise `P₁ = π⁻¹(0 × K)`
(`Chapter IV §4` of the classification).

The argument is elementary.  Let `U ≤ K × K` have order `8` and be totally isotropic, and
suppose `u₀ = (a, ·) ∈ U` with `a ≠ 0`.  Then for `v = (0,y) ∈ U` the isotropy condition reads
`β(u₀,v) = ε·a⁴·y⁴ = 0`, so `y = 0`: the first projection `π : U → K` is injective, hence
(equal finite cardinalities) surjective, so `U` is the graph of a function `f : K → K`.

Writing the two isotropy conditions `β((x,f x),(t,f t)) = 0` and `β((1,f 1),(t,f t)) = 0` in
coordinates and eliminating `f`, the coefficient of `ε` drops out (characteristic two) and one
obtains the *pure* polynomial identity

  `x·t·(x+t)·(1+x)·(t+1)·(t+1+x) = 0    for all x, t ∈ K`,

which is false: take `a ∉ {0,1}` and `t ∉ {0,a,1,1+a}`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Work.Hering.AppVIII

open Work.Higman

/-- `K = KC 1 = GF(8)` has eight elements. -/
lemma natCardKC1 : Nat.card (KC 1) = 8 := by
  have h := GaloisField.card 2 3 (by norm_num)
  norm_num at h
  exact h

/-- The characteristic-two identity obtained by combining the two isotropy conditions
`B x t = 0` and `B 1 t = 0` (`B` being the coordinate form of `betaP` on pairs of graph
points): the terms involving `ε` cancel in pairs and a factorisation remains. -/
lemma betaP_polar_identity_local (ε : KC 1) (F : KC 1 → KC 1) (x t : KC 1) :
    (x * t ^ 2 + t * x ^ 2 + ε * (x ^ 4 * F t + t ^ 4 * F x))
      + x ^ 4 * (1 * t ^ 2 + t * 1 ^ 2 + ε * (1 ^ 4 * F t + t ^ 4 * F 1))
      + t ^ 4 * (1 * x ^ 2 + x * 1 ^ 2 + ε * (1 ^ 4 * F x + x ^ 4 * F 1))
    = x * t * (x + t) * (1 + x) * (t + 1) * (t + 1 + x) := by
  have h2 : (2 : KC 1) = 0 := CharTwo.two_eq_zero
  have h4 : (4 : KC 1) = 0 := by
    have : ((4 : ℕ) : KC 1) = 0 := by rw [CharTwo.natCast_eq_mod]; norm_num
    exact this
  ring_nf
  simp only [h2, h4, mul_zero, zero_mul, add_zero, zero_add]

/-- A subgroup `U ≤ K × K` of order `8` on which the first projection is injective is the graph
of a function `K → K`. -/
lemma isotropic_aux_graph_local (U : AddSubgroup (KC 1 × KC 1)) (hcard : Nat.card U = 8)
    (hW : ∀ v : KC 1 × KC 1, v ∈ U → v.1 = 0 → v = 0) :
    ∃ f : KC 1 → KC 1, ∀ x : KC 1, (x, f x) ∈ U := by
  classical
  haveI : Fintype ↥U := Fintype.ofFinite ↥U
  haveI : Fintype (KC 1) := Fintype.ofFinite (KC 1)
  have hcardK : Fintype.card (KC 1) = 8 := (Nat.card_eq_fintype_card).symm.trans natCardKC1
  have hcardU : Fintype.card ↥U = 8 := (Nat.card_eq_fintype_card).symm.trans hcard
  let π : ↥U → KC 1 := fun w => (w : KC 1 × KC 1).1
  have hπinj : Function.Injective π := by
    intro a b hab
    have hab' : (a : KC 1 × KC 1).1 = (b : KC 1 × KC 1).1 := hab
    have hmem : ((a : KC 1 × KC 1) - (b : KC 1 × KC 1)) ∈ U := U.sub_mem a.2 b.2
    have h1 : ((a : KC 1 × KC 1) - (b : KC 1 × KC 1)).1 = 0 := by
      rw [Prod.fst_sub, hab', sub_self]
    exact Subtype.ext (sub_eq_zero.mp (hW _ hmem h1))
  have hsurj : Function.Surjective π := by
    have himg : (Finset.univ.image π).card = Fintype.card (KC 1) := by
      rw [Finset.card_image_of_injective _ hπinj, Finset.card_univ, hcardU, hcardK]
    have huniv := Finset.eq_univ_of_card (Finset.univ.image π) himg
    intro x
    have hx : x ∈ (Finset.univ.image π : Finset (KC 1)) := by rw [huniv]; exact Finset.mem_univ x
    rw [Finset.mem_image] at hx
    obtain ⟨w, _, hw⟩ := hx
    exact ⟨w, hw⟩
  refine ⟨fun x => (((hsurj x).choose : ↥U) : KC 1 × KC 1).2, ?_⟩
  intro x
  have hspec : (((hsurj x).choose : ↥U) : KC 1 × KC 1).1 = x := (hsurj x).choose_spec
  have hp : (((hsurj x).choose : ↥U) : KC 1 × KC 1)
      = (x, (((hsurj x).choose : ↥U) : KC 1 × KC 1).2) := Prod.ext hspec rfl
  rw [← hp]
  exact (hsurj x).choose.2

/-- **`W = {u | u.1 = 0}` is the unique totally isotropic subspace of `K × K` of order `8`.** -/
theorem isotropic_unique (ε : Work.Hering.AppVIII.KC 1) (hε : ε ≠ 0)
    (U : AddSubgroup (Work.Hering.AppVIII.KC 1 × Work.Hering.AppVIII.KC 1))
    (hcard : Nat.card U = 8)
    (hiso : ∀ u ∈ U, ∀ v ∈ U, Work.Hering.AppVIII.betaP ε u v = 0) :
    ∀ u ∈ U, u.1 = 0 := by
  classical
  intro u0 hu0
  by_contra hx0
  -- Step 1: any element of `U` with vanishing first coordinate is zero.
  have hW : ∀ v : KC 1 × KC 1, v ∈ U → v.1 = 0 → v = 0 := by
    intro v hv hv1
    have hb : betaP ε u0 v = 0 := hiso u0 hu0 v hv
    have hb' : ε * (u0.1 ^ 4 * v.2 ^ 4) = 0 := by
      have he : betaP ε u0 v = ε * (u0.1 ^ 4 * v.2 ^ 4) := by simp [betaP, hv1]
      rw [← he]; exact hb
    have hne : ε * u0.1 ^ 4 ≠ 0 := mul_ne_zero hε (pow_ne_zero 4 hx0)
    have h4 : v.2 ^ 4 = 0 := by
      have h : (ε * u0.1 ^ 4) * v.2 ^ 4 = 0 := by rw [mul_assoc]; exact hb'
      exact (mul_eq_zero.mp h).resolve_left hne
    have hv2 : v.2 = 0 := (pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).mp h4
    exact Prod.ext hv1 hv2
  -- Step 2: `U` is the graph of a function `f : K → K`.
  obtain ⟨f, hf⟩ := isotropic_aux_graph_local U hcard hW
  -- Step 3: the two isotropy conditions in coordinates.
  have hB : ∀ x t : KC 1,
      x * t ^ 2 + t * x ^ 2 + ε * (x ^ 4 * (f t) ^ 4 + t ^ 4 * (f x) ^ 4) = 0 := by
    intro x t
    have h1 : betaP ε (x, f x) (t, f t) = 0 := hiso _ (hf x) _ (hf t)
    have he : betaP ε (x, f x) (t, f t)
        = x * t ^ 2 + t * x ^ 2 + ε * (x ^ 4 * (f t) ^ 4 + t ^ 4 * (f x) ^ 4) := by
      simp [betaP]
    rw [he] at h1; exact h1
  -- Step 4: combine them into the pure factorised identity.
  have hfac : ∀ x t : KC 1, x * t * (x + t) * (1 + x) * (t + 1) * (t + 1 + x) = 0 := by
    intro x t
    rw [← betaP_polar_identity_local ε (fun s => (f s) ^ 4) x t]
    rw [hB x t, hB 1 t, hB 1 x]
    ring
  -- Step 5: pick `a ∉ {0,1}` and `t ∉ {0,a,1,1+a}` (possible since `K` has eight elements).
  haveI : Fintype (KC 1) := Fintype.ofFinite (KC 1)
  have hcardK : Fintype.card (KC 1) = 8 := (Nat.card_eq_fintype_card).symm.trans natCardKC1
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0, 1} : Finset (KC 1))) (t := Finset.univ) (by
        rw [Finset.card_univ, hcardK]
        calc ({0, 1} : Finset (KC 1)).card ≤ 2 := Finset.card_le_two
          _ < 8 := by norm_num)
  have ha0 : a ≠ 0 := fun h => ha (by simp [h])
  have ha1 : a ≠ 1 := fun h => ha (by simp [h])
  obtain ⟨t, _, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0, a, 1, 1 + a} : Finset (KC 1))) (t := Finset.univ) (by
        rw [Finset.card_univ, hcardK]
        calc ({0, a, 1, 1 + a} : Finset (KC 1)).card
            ≤ (({0, 1} : Finset (KC 1)) ∪ ({a, 1 + a} : Finset (KC 1))).card := by
              apply Finset.card_le_card
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at hx ⊢
              tauto
          _ ≤ ({0, 1} : Finset (KC 1)).card + ({a, 1 + a} : Finset (KC 1)).card :=
              Finset.card_union_le _ _
          _ ≤ 2 + 2 := add_le_add Finset.card_le_two Finset.card_le_two
          _ = 4 := by norm_num
          _ < 8 := by norm_num)
  have ht0 : t ≠ 0 := fun h => ht (by simp [h])
  have hta : t ≠ a := fun h => ht (by simp [h])
  have ht1 : t ≠ 1 := fun h => ht (by simp [h])
  have ht1a : t ≠ 1 + a := fun h => ht (by simp [h])
  -- Step 6: the left-hand side is a product of nonzero field elements, hence nonzero.
  have hne' : a * t * (a + t) * (1 + a) * (t + 1) * (t + 1 + a) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · apply mul_ne_zero
            · exact ha0
            · exact ht0
          · intro h; exact hta (CharTwo.add_eq_zero.mp h).symm
        · intro h; exact ha1 (CharTwo.add_eq_zero.mp h).symm
      · intro h; exact ht1 (CharTwo.add_eq_zero.mp h)
    · intro h
      apply ht1a
      have h1 : t + 1 = 0 + a := CharTwo.add_eq_iff_eq_add.mp h
      rw [zero_add] at h1
      have h2 : t = a + 1 := CharTwo.add_eq_iff_eq_add.mp h1
      rw [h2, add_comm]
  exact hne' (hfac a t)

end Work.Hering.AppVIII
