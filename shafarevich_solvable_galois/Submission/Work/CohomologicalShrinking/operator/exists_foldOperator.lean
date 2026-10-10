import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.FreeGroup.Basic
import Submission.Work.CohomologicalShrinking.Functorial
import Submission.Work.CohomologicalShrinking.modsquare.squareQuotientToFun_bijective
import Submission.Work.CohomologicalShrinking.modsquare.squareQuotientToFun_smul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

attribute [local instance] Classical.decEq

set_option maxHeartbeats 1000000

/-!
# The folding operator on `F(r·n)/F(r·n)²`

For a free `G`-operator group `F(d) = FreeGroup (Fin d × G)` the square quotient
`F(d)/F(d)² = F(d)/F(d)^p[F(d),F(d)]` is the free `𝔽_p[G]`-module `𝔽_p[G]^d`
(`Work.CohomologicalShrinking.modsquare.squareQuotientToFun_bijective`).

This file constructs, for `a : Fin r → 𝔽_p` with `a k₀ = 1`, the folded operator
homomorphism `ψ : F(r·n) → F(n)`, `x_{(k,j),g} ↦ x_{(j,g)}^{a_k}`, together with the
canonical linear equivalence `e : (F(n)/F(n)²)^r ≅ F(r·n)/F(r·n)²` making the diagram
`ψ̄ ∘ e = φ_a` commute, where `φ_a` is the folding map of `Work.Shrinking.foldMap`.
-/

namespace Work.CohomologicalShrinking.operator

open Work.CohomologicalShrinking

/-! ## The canonical identification `F(d)/F(d)² ≅ 𝔽_p[G]^d` -/

noncomputable def sqEquiv (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G] (d : ℕ) :
    squareQuotient p G d ≃ₗ[ZMod p] (Fin d × G → ZMod p) :=
  LinearEquiv.ofBijective (squareQuotientToFun p G d)
    (modsquare.squareQuotientToFun_bijective p G d)

theorem sqEquiv_apply (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G] (d : ℕ)
    (x : squareQuotient p G d) :
    sqEquiv p G d x = squareQuotientToFun p G d x :=
  LinearEquiv.ofBijective_apply _ x

theorem sqEquiv_genMk (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G] (d : ℕ)
    (x : Fin d × G) : sqEquiv p G d (genMk p G d x) = Pi.single x (1 : ZMod p) := by
  rw [sqEquiv_apply, squareQuotientToFun_genMk]

theorem sqEquiv_symm_single (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G] (d : ℕ)
    (x : Fin d × G) : (sqEquiv p G d).symm (Pi.single x (1 : ZMod p)) = genMk p G d x := by
  rw [LinearEquiv.symm_apply_eq, sqEquiv_genMk]

theorem sqEquiv_smul (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G] (d : ℕ) (g : G)
    (x : squareQuotient p G d) : sqEquiv p G d (g • x) = g • sqEquiv p G d x :=
  modsquare.squareQuotientToFun_smul p G d g x

theorem sqEquiv_symm_smul (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G] (d : ℕ)
    (g : G) (x : Fin d × G → ZMod p) :
    (sqEquiv p G d).symm (g • x) = g • (sqEquiv p G d).symm x := by
  apply (sqEquiv p G d).injective
  rw [sqEquiv_smul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- The action on the generators of `F(d)/F(d)²`. -/
theorem smul_genMk (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G] (d : ℕ) (g : G)
    (x : Fin d × G) : g • genMk p G d x = genMk p G d (x.1, g * x.2) := by
  apply (sqEquiv p G d).injective
  rw [sqEquiv_smul, sqEquiv_genMk, sqEquiv_genMk, modsquare.smul_pi_single]

/-! ## Elementary computations with `Pi.single` -/

theorem piCongrRight_pi_single (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    (n r : ℕ) (k : Fin r) (w : squareQuotient p G n) :
    (LinearEquiv.piCongrRight (fun _ : Fin r => sqEquiv p G n)) (Pi.single k w)
      = Pi.single k (sqEquiv p G n w) := by
  ext i
  rw [LinearEquiv.piCongrRight_apply, Pi.single_apply, Pi.single_apply]
  by_cases h : i = k <;> simp [h]

theorem smul_pi_single_pi (p : ℕ) (G : Type*) [Group G] (r n : ℕ) (g : G) (k : Fin r)
    (w : squareQuotient p G n) :
    g • (Pi.single k w : Fin r → squareQuotient p G n) = Pi.single k (g • w) := by
  ext i
  rw [Pi.smul_apply, Pi.single_apply, Pi.single_apply]
  by_cases h : i = k <;> simp [h]

theorem curry_symm_pi_single (p : ℕ) (V V₂ : Type*) [DecidableEq V] [DecidableEq V₂]
    (M : Type*) [AddCommMonoid M] [Module (ZMod p) M] (i : V) (j : V₂) (c : M) :
    (LinearEquiv.curry (ZMod p) M V V₂).symm (Pi.single i (Pi.single j c))
      = Pi.single (i, j) c := by
  ext q
  obtain ⟨a, b⟩ := q
  rw [LinearEquiv.coe_curry_symm, Function.uncurry_apply_pair]
  rcases eq_or_ne a i with ha | ha
  · subst ha
    rcases eq_or_ne b j with hb | hb
    · subst hb
      rw [Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_same,
        Pi.single_eq_of_ne (M := fun _ : V₂ => M) hb c,
        Pi.single_eq_of_ne (M := fun _ : V × V₂ => M)
          (fun hc => hb (Prod.ext_iff.mp hc).2) c]
  · rw [Pi.single_eq_of_ne (M := fun _ : V => (V₂ → M)) ha
        (Pi.single j c : V₂ → M),
      Pi.single_eq_of_ne (M := fun _ : V × V₂ => M)
        (fun hc => ha (Prod.ext_iff.mp hc).1) c]
    rfl

theorem funCongrLeft_symm_pi_single (p : ℕ) {m n : Type*} [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) (M : Type*) [AddCommMonoid M] [Module (ZMod p) M] (i : m) (c : M) :
    LinearEquiv.funCongrLeft (ZMod p) M e.symm (Pi.single i c) = Pi.single (e i) c := by
  ext j
  rw [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  by_cases h : j = e i
  · subst h; simp
  · rw [Pi.single_eq_of_ne (M := fun _ : m => M)
        (show e.symm j ≠ i from fun hc => h (by rw [← hc]; exact (e.apply_symm_apply j).symm)) c,
      Pi.single_eq_of_ne (M := fun _ : n => M) h c]

/-! ## The index equivalence `Fin r × (Fin n × G) ≃ Fin (r·n) × G` -/

def idxEquiv (r n : ℕ) (G : Type*) : Fin r × (Fin n × G) ≃ Fin (r * n) × G :=
  (Equiv.prodAssoc (Fin r) (Fin n) G).symm.trans (finProdFinEquiv.prodCongr (Equiv.refl G))

theorem idxEquiv_apply (r n : ℕ) (G : Type*) (k : Fin r) (j : Fin n) (g : G) :
    idxEquiv r n G (k, (j, g)) = (finProdFinEquiv (k, j), g) := rfl

/-! ## The folding linear equivalence `e` -/

noncomputable def foldAux (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    (r n : ℕ) : (Fin r → squareQuotient p G n) ≃ₗ[ZMod p] (Fin (r * n) × G → ZMod p) :=
  (LinearEquiv.piCongrRight (fun _ : Fin r => sqEquiv p G n)).trans
    ((LinearEquiv.curry (ZMod p) (ZMod p) (Fin r) (Fin n × G)).symm.trans
      (LinearEquiv.funCongrLeft (ZMod p) (ZMod p) (idxEquiv r n G).symm))

noncomputable def foldEquiv (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    (r n : ℕ) : (Fin r → squareQuotient p G n) ≃ₗ[ZMod p] squareQuotient p G (r * n) :=
  (foldAux p G r n).trans (sqEquiv p G (r * n)).symm

noncomputable def foldFun (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    (r n : ℕ) : (Fin r → squareQuotient p G n) →ₗ[ZMod p] (Fin (r * n) × G → ZMod p) :=
  (foldAux p G r n).toLinearMap

theorem sqEquiv_foldEquiv (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G] (r n : ℕ)
    (x : Fin r → squareQuotient p G n) :
    sqEquiv p G (r * n) (foldEquiv p G r n x) = foldFun p G r n x := by
  show sqEquiv p G (r * n) ((sqEquiv p G (r * n)).symm (foldFun p G r n x)) = foldFun p G r n x
  rw [LinearEquiv.apply_symm_apply]

theorem foldAux_apply_single (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    (r n : ℕ) (k : Fin r) (j : Fin n) (g : G) :
    foldAux p G r n (Pi.single k (genMk p G n (j, g)))
      = Pi.single (finProdFinEquiv (k, j), g) (1 : ZMod p) := by
  show (LinearEquiv.funCongrLeft (ZMod p) (ZMod p) (idxEquiv r n G).symm)
      ((LinearEquiv.curry (ZMod p) (ZMod p) (Fin r) (Fin n × G)).symm
        ((LinearEquiv.piCongrRight (fun _ : Fin r => sqEquiv p G n))
          (Pi.single k (genMk p G n (j, g))))) = _
  rw [show (LinearEquiv.piCongrRight (fun _ : Fin r => sqEquiv p G n))
        (Pi.single k (genMk p G n (j, g))) = Pi.single k (Pi.single (j, g) (1 : ZMod p)) from by
      rw [piCongrRight_pi_single, sqEquiv_genMk]]
  rw [show (LinearEquiv.curry (ZMod p) (ZMod p) (Fin r) (Fin n × G)).symm
        (Pi.single k (Pi.single (j, g) (1 : ZMod p)))
      = Pi.single (k, (j, g)) (1 : ZMod p) from curry_symm_pi_single p (Fin r) (Fin n × G)
          (ZMod p) k (j, g) 1]
  rw [show (LinearEquiv.funCongrLeft (ZMod p) (ZMod p) (idxEquiv r n G).symm)
        (Pi.single (k, (j, g)) (1 : ZMod p))
      = Pi.single (finProdFinEquiv (k, j), g) (1 : ZMod p) from by
      rw [funCongrLeft_symm_pi_single p (idxEquiv r n G) (ZMod p) (k, (j, g)) 1, idxEquiv_apply]]

theorem foldEquiv_apply_single (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    (r n : ℕ) (k : Fin r) (j : Fin n) (g : G) :
    foldEquiv p G r n (Pi.single k (genMk p G n (j, g)))
      = genMk p G (r * n) (finProdFinEquiv (k, j), g) := by
  rw [show foldEquiv p G r n (Pi.single k (genMk p G n (j, g)))
        = (sqEquiv p G (r * n)).symm (foldAux p G r n (Pi.single k (genMk p G n (j, g))))
        from rfl,
      foldAux_apply_single, sqEquiv_symm_single]

theorem foldFun_apply_idx (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    (r n : ℕ) (u : Fin r → squareQuotient p G n) (k : Fin r) (j : Fin n) (g : G) :
    foldFun p G r n u (idxEquiv r n G (k, (j, g))) = sqEquiv p G n (u k) (j, g) := by
  show (LinearEquiv.funCongrLeft (ZMod p) (ZMod p) (idxEquiv r n G).symm)
      ((LinearEquiv.curry (ZMod p) (ZMod p) (Fin r) (Fin n × G)).symm
        ((LinearEquiv.piCongrRight (fun _ : Fin r => sqEquiv p G n)) u))
      (idxEquiv r n G (k, (j, g))) = sqEquiv p G n (u k) (j, g)
  rw [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Equiv.symm_apply_apply,
    LinearEquiv.coe_curry_symm, Function.uncurry_apply_pair, LinearEquiv.piCongrRight_apply]

theorem foldFun_smul (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G] (r n : ℕ)
    (g : G) (u : Fin r → squareQuotient p G n) :
    foldFun p G r n (g • u) = g • foldFun p G r n u := by
  funext x
  obtain ⟨⟨k, j, g'⟩, rfl⟩ := (idxEquiv r n G).surjective x
  rw [foldFun_apply_idx]
  conv_lhs => rw [Pi.smul_apply, sqEquiv_smul, smul_prodFun_apply]
  conv_rhs => rw [smul_prodFun_apply]
  rw [idxEquiv_apply]
  rw [← idxEquiv_apply]
  rw [foldFun_apply_idx]

/-! ## The folding operator homomorphism `ψ` -/

noncomputable def foldGen (p : ℕ) (G : Type*) [Group G] (r n : ℕ) (a : Fin r → ZMod p) :
    Fin (r * n) × G → Work.Shrinking.freeOperatorGroup G n :=
  fun x => FreeGroup.of ((finProdFinEquiv.symm x.1).2, x.2) ^ (a (finProdFinEquiv.symm x.1).1).val

noncomputable def foldψ (p : ℕ) (G : Type*) [Group G] (r n : ℕ) (a : Fin r → ZMod p) :
    Work.Shrinking.freeOperatorGroup G (r * n) →* Work.Shrinking.freeOperatorGroup G n :=
  FreeGroup.lift (foldGen p G r n a)

theorem foldψ_of (p : ℕ) (G : Type*) [Group G] (r n : ℕ) (a : Fin r → ZMod p)
    (x : Fin (r * n) × G) :
    foldψ p G r n a (FreeGroup.of x) = foldGen p G r n a x :=
  FreeGroup.lift_apply_of

theorem foldψ_of_finProd (p : ℕ) (G : Type*) [Group G] (r n : ℕ) (a : Fin r → ZMod p)
    (k : Fin r) (j : Fin n) (g : G) :
    foldψ p G r n a (FreeGroup.of (finProdFinEquiv (k, j), g))
      = FreeGroup.of (j, g) ^ (a k).val := by
  rw [foldψ_of]
  simp only [foldGen, Equiv.symm_apply_apply]

theorem foldψ_surjective (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (r n : ℕ)
    (a : Fin r → ZMod p) {k₀ : Fin r} (ha : a k₀ = 1) :
    Function.Surjective (foldψ p G r n a) := by
  rw [← MonoidHom.range_eq_top, foldψ, FreeGroup.range_lift_eq_closure]
  rw [eq_top_iff, ← FreeGroup.closure_range_of (Fin n × G)]
  refine (Subgroup.closure_le (Subgroup.closure (Set.range (foldGen p G r n a)))).mpr ?_
  rintro y ⟨⟨i, g⟩, rfl⟩
  have hval : (a k₀).val = 1 := by
    rw [ha, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt]
  have hfg : foldGen p G r n a (finProdFinEquiv (k₀, i), g) = FreeGroup.of (i, g) := by
    simp only [foldGen, Equiv.symm_apply_apply, hval, pow_one]
  rw [← hfg]
  exact Subgroup.subset_closure (Set.mem_range_self _)

theorem foldψ_smul (p : ℕ) (G : Type*) [Group G] (r n : ℕ) (a : Fin r → ZMod p) (g : G)
    (y : Work.Shrinking.freeOperatorGroup G (r * n)) :
    foldψ p G r n a (g • y) = g • foldψ p G r n a y := by
  have key : ∀ x : Fin (r * n) × G,
      foldψ p G r n a (g • FreeGroup.of x) = g • foldψ p G r n a (FreeGroup.of x) := by
    intro x
    rw [Work.Shrinking.smul_freeOperator_of, foldψ_of, foldψ_of]
    simp only [foldGen]
    rw [smul_pow', Work.Shrinking.smul_freeOperator_of]
  induction y using FreeGroup.induction_on with
  | one => simp
  | of x => exact key x
  | inv_of x ih =>
      simp only [Work.Shrinking.smul_freeOperatorGroup_eq] at ih ⊢
      simp only [map_inv, ih]
  | mul x y ihx ihy =>
      simp only [Work.Shrinking.smul_freeOperatorGroup_eq] at ihx ihy ⊢
      simp only [map_mul, ihx, ihy]

/-! ## The class of a power in `F(d)/F(d)²` -/

theorem squareQuotientClass_pow (p : ℕ) (G : Type*) [Group G] (d : ℕ)
    (w : Work.Shrinking.freeOperatorGroup G d) (c : ℕ) :
    modsquare.squareQuotientClass p G d (w ^ c) = c • modsquare.squareQuotientClass p G d w := by
  induction c with
  | zero => rw [pow_zero, modsquare.squareQuotientClass_one, zero_smul]
  | succ k ih => rw [pow_succ, modsquare.squareQuotientClass_mul, ih, succ_nsmul]

/-! ## The induced map on `F(d)/F(d)²` on generators -/

theorem quotMapLin_genMk (p : ℕ) (G : Type*) [Group G] {m n : ℕ}
    (ψ : Work.Shrinking.freeOperatorGroup G m →* Work.Shrinking.freeOperatorGroup G n)
    (hψ : Function.Surjective ψ) (x : Fin m × G) :
    quotMapLin p G ψ hψ (genMk p G m x)
      = modsquare.squareQuotientClass p G n (ψ (FreeGroup.of x)) := by
  show Additive.ofMul (pCentralMapMul p ψ hψ 0 (Additive.toMul (genMk p G m x)))
      = modsquare.squareQuotientClass p G n (ψ (FreeGroup.of x))
  rw [genMk, toMul_ofMul, pCentralMapMul, QuotientGroup.map_mk', modsquare.squareQuotientClass]
  rfl

/-! ## The spanning statements -/

theorem span_pi_single_one (p d : ℕ) (G : Type*) [Fintype G] :
    Submodule.span (ZMod p)
      (Set.range (fun x : Fin d × G => (Pi.single x (1 : ZMod p) : Fin d × G → ZMod p))) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun f => ?_
  rw [← modsquare.sum_smul_pi_single p (Fin d × G) f]
  exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)

theorem span_genMk_pi (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G] (r n : ℕ) :
    Submodule.span (ZMod p)
      (Set.range (fun x : Fin r × (Fin n × G) =>
        (Pi.single x.1 (genMk p G n x.2) : Fin r → squareQuotient p G n))) = ⊤ := by
  let Φ : (Fin r → squareQuotient p G n) ≃ₗ[ZMod p] (Fin (r * n) × G → ZMod p) :=
    foldAux p G r n
  set s : Set (Fin r → squareQuotient p G n) :=
    Set.range (fun x : Fin r × (Fin n × G) =>
      (Pi.single x.1 (genMk p G n x.2) : Fin r → squareQuotient p G n)) with hs
  have hspan' : Submodule.span (ZMod p) (Set.range (fun y : Fin r × (Fin n × G) =>
      (Pi.single (idxEquiv r n G y) (1 : ZMod p) : Fin (r * n) × G → ZMod p))) = ⊤ := by
    refine Submodule.eq_top_iff'.mpr fun z => ?_
    rw [← modsquare.sum_smul_pi_single p (Fin (r * n) × G) z]
    rw [← Fintype.sum_equiv (idxEquiv r n G)
      (fun y : Fin r × (Fin n × G) =>
        z (idxEquiv r n G y) • (Pi.single (idxEquiv r n G y) (1 : ZMod p) :
          Fin (r * n) × G → ZMod p))
      (fun y : Fin (r * n) × G => z y • (Pi.single y (1 : ZMod p) : Fin (r * n) × G → ZMod p))
      (fun _ => rfl)]
    exact Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
  have hmap : Submodule.map Φ.toLinearMap (Submodule.span (ZMod p) s) = ⊤ := by
    rw [Submodule.map_span]
    have himg : (⇑(Φ : (Fin r → squareQuotient p G n) →ₗ[ZMod p]
          (Fin (r * n) × G → ZMod p))) '' s
        = Set.range (fun y : Fin r × (Fin n × G) =>
            (Pi.single (idxEquiv r n G y) (1 : ZMod p) : Fin (r * n) × G → ZMod p)) := by
      rw [hs, ← Set.range_comp]
      congr 1
      funext x
      obtain ⟨k, j, g⟩ := x
      show foldAux p G r n (Pi.single k (genMk p G n (j, g))) = _
      rw [foldAux_apply_single, idxEquiv_apply]
    rw [himg, hspan']
  have hinj : Function.Injective (Submodule.map Φ.toLinearMap) :=
    Submodule.map_injective_of_injective Φ.injective
  have htop : Submodule.map Φ.toLinearMap ⊤ = ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top.mpr Φ.surjective]
  exact hinj (by rw [hmap, htop])

/-! ## Equivariance and the commuting square -/

theorem foldEquiv_smul (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    (r n : ℕ) (g : G) (z : Fin r → squareQuotient p G n) :
    foldEquiv p G r n (g • z) = g • foldEquiv p G r n z := by
  apply (sqEquiv p G (r * n)).injective
  rw [sqEquiv_foldEquiv, sqEquiv_smul, sqEquiv_foldEquiv, foldFun_smul]

theorem foldEquiv_comp_quotMapLin (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    (r n : ℕ) (a : Fin r → ZMod p) {k₀ : Fin r} (ha : a k₀ = 1) :
    (quotMapLin p G (foldψ p G r n a) (foldψ_surjective p G r n a ha)).comp
        (foldEquiv p G r n).toLinearMap
      = Work.Shrinking.foldMap (M := squareQuotient p G n) a := by
  refine LinearMap.ext_on (span_genMk_pi p G r n) ?_
  rintro w ⟨x, rfl⟩
  obtain ⟨k, j, g⟩ := x
  show quotMapLin p G (foldψ p G r n a) (foldψ_surjective p G r n a ha)
      (foldEquiv p G r n (Pi.single k (genMk p G n (j, g))))
    = Work.Shrinking.foldMap (M := squareQuotient p G n) a (Pi.single k (genMk p G n (j, g)))
  rw [foldEquiv_apply_single, quotMapLin_genMk, foldψ_of_finProd, squareQuotientClass_pow,
    modsquare.squareQuotientClass_of, Work.Shrinking.foldMap_apply_single]
  conv_rhs => rw [← ZMod.natCast_zmod_val (a k)]
  rw [Nat.cast_smul_eq_nsmul]

/-! ## The folding operator -/

theorem exists_foldOperator (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    (r n : ℕ) {k₀ : Fin r} (a : Fin r → ZMod p) (ha : a k₀ = 1) :
    ∃ (e : (Fin r → Work.CohomologicalShrinking.squareQuotient p G n) ≃ₗ[ZMod p]
          Work.CohomologicalShrinking.squareQuotient p G (r * n))
      (ψ : Work.Shrinking.freeOperatorGroup G (r * n) →* Work.Shrinking.freeOperatorGroup G n)
      (hψ : Function.Surjective ψ),
      (∀ (k : Fin r) (j : Fin n) (g : G),
        e (Pi.single k (Work.CohomologicalShrinking.genMk p G n (j, g)))
          = Work.CohomologicalShrinking.genMk p G (r * n) (finProdFinEquiv (k, j), g)) ∧
      (∀ (g : G) (z : Fin r → Work.CohomologicalShrinking.squareQuotient p G n), e (g • z) = g • e z) ∧
      (∀ (g : G) (y : Work.Shrinking.freeOperatorGroup G (r * n)), ψ (g • y) = g • ψ y) ∧
      (Work.CohomologicalShrinking.quotMapLin p G ψ hψ).comp e.toLinearMap
        = Work.Shrinking.foldMap (M := Work.CohomologicalShrinking.squareQuotient p G n) a := by
  exact ⟨foldEquiv p G r n, foldψ p G r n a, foldψ_surjective p G r n a ha,
    fun k j g => foldEquiv_apply_single p G r n k j g,
    fun g z => foldEquiv_smul p G r n g z,
    fun g y => foldψ_smul p G r n a g y,
    foldEquiv_comp_quotMapLin p G r n a ha⟩

end Work.CohomologicalShrinking.operator
