import Mathlib
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.KafzHonest` — FS `thm:Kafz` for the honest model (`H2ndF`)

Framework for `Work.BoseBoxFock.model_kafz`; route in
`Submission/Work/BoseBoxFock/KAFZ_HONEST_ROUTE.md`.  The plan (FS §8, `thm:Kafz`):

1. **dictionary.**  Each row of `H2ndF` is transported by `Work.BoseB4.split` to a
   finite sum of anti-normal monomials `Σᵢ a₀^{pᵢ}(a₀†)^{qᵢ}(lift Bᵢ)`
   (`Work.BoseB4.Kafz_lattice` gives the coherent-state identity);
2. **symbol comparison.**  The anti-Wick symbol `Σᵢ z^{pᵢ}z̄^{qᵢ}Bᵢ` is compared
   with FS `eq:Kz`'s `KzOpFS(ρ_z)`;
3. **assembly.**  `Kafz_lower_bound_pointwise` plus the window and the Gaussian
   moments.

This file holds part 1 (the dictionary) and its infrastructure.

## The dictionary, row by row

`H2ndF`'s rows (`Defs.lean`, in order), with `a = annOf m (f k)`, `ta = annOf m (g s)`,
`a0 = ann m 0`, `a0d = cre m 0`, `W_k := creOfE (f k) ∘ annOfE (f k)` and the honest
data (`f k 0 = 0`, `g s 0 = 0`):

| row | operator | transported `Σ monoOp p q B` |
|---|---|---|
| `Hkin` | `Σ_k τ_k (ad k ∘ a k)` | `(0,0)`, `B = Σ_k τ_k W_k` |
| `Hgap` | `(b/2ℓ²)(N − n₀)` | `(0,0)`, `B = (b/2ℓ²)Σ_{l≠0} (creC l ∘ annC l)` |
| `HgapH` | `(ε_Tb/2d²ℓ²) NH` | `(0,0)`, honest `NH` transported |
| `Hcontact` | `½ℓ⁻³(ĝ₀+Ŵ₁ω₀)a₀†a₀†a₀a₀` | `monoOp 2 2 1 − 4 monoOp 1 1 1 + 2 monoOp 0 0 1` |
| `Hmu` | `−μĝ₀a₀†a₀` | `monoOp 1 1 1 − monoOp 0 0 1` |
| `HW` | `ℓ⁻³Σ_k(Ŵ₁k+Ŵ₁ωk)a₀†a_k†a_ka₀` | `(1,1)` with `B = Σ_k(Ŵ₁k+Ŵ₁ωk)W_k`, minus the `(0,0)` slot |
| `Hbog` | `½ℓ⁻³Σ_kŴ₁k(a₀†a₀†a_ka_{−k}+h.c.)` | `(0,2)` resp. `(2,0)` with `B = a_ka_{−k}` |
| `Hchi` | `Σ_k χ̂_k(L0a_k†a₀ + a₀†a_kL0)` | `ℓ⁻³Ŵ₁0(monoOp 2 1 B − 2monoOp 1 0 B) − μŴ₁0 monoOp 1 0 B` (+ adjoint) |
| `HchiOm` | `Σ_{s≠0}χ̂²_s(L1ã_s†a₀ + a₀†ã_sL1)` | same shape with `Ŵ₁ω0`, `ã_s` |
| `Hnn` | `(L0+L1)Σ_ka_k†a_k` | `(1,1)` and `(0,0)` on `Σ_k n_k` |
| `HQ3` | `ℓ⁻³Σ_sΣ_k f_L(s)Ŵ₁(k)a₀†ã_s†a_{s−k}a_k + h.c.` | `(0,1)`, `(1,0)` |
-/

noncomputable section

open scoped BigOperators lp

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false

variable {m : ℕ} [NeZero m]

/-! ## 1. Splitting a `Fin m`-sum into the condensate coordinate and the excited ones -/

/-- The `Fin m`-sum splits as the `0`-term plus the sum over the excited coordinates. -/
lemma sum_univ_eq_zero_add {M : Type*} [AddCommMonoid M] (f : Fin m → M) :
    (∑ l : Fin m, f l) = f 0 + ∑ l : Excited m, f l.1 := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin m)), add_comm]
  congr 1
  exact Finset.sum_subtype ((Finset.univ : Finset (Fin m)).erase 0) (fun x => by simp) f

/-! ## 2. The honest superposed modes on the spectator space -/

/-- The spectator image of `annOf m φ` (`φ 0 = 0`). -/
noncomputable def annOfE (φ : Fin m → ℝ) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ l : Excited m, ((φ l.1 : ℝ) : ℂ) • annC (Excited m) l

/-- The spectator image of `creOf m φ` (`φ 0 = 0`). -/
noncomputable def creOfE (φ : Fin m → ℝ) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ l : Excited m, ((φ l.1 : ℝ) : ℂ) • creC (Excited m) l

/-- `annOf m φ` only sees the excited coordinates when `φ 0 = 0`. -/
lemma annOf_eq_sum_excited (φ : Fin m → ℝ) (h0 : φ 0 = 0) :
    annOf m φ = ∑ l : Excited m, (φ l.1) • ann m l.1 := by
  rw [annOf, sum_univ_eq_zero_add (fun l => (φ l) • ann m l), h0, zero_smul, zero_add]

/-- `creOf m φ` only sees the excited coordinates when `φ 0 = 0`. -/
lemma creOf_eq_sum_excited (φ : Fin m → ℝ) (h0 : φ 0 = 0) :
    creOf m φ = ∑ l : Excited m, (φ l.1) • cre m l.1 := by
  rw [creOf, sum_univ_eq_zero_add (fun l => (φ l) • cre m l), h0, zero_smul, zero_add]

/-- **The annihilation dictionary**: `split ∘ annOf m φ = lift (annOfE φ) ∘ split`
for `φ 0 = 0`. -/
theorem split_annOf (φ : Fin m → ℝ) (h0 : φ 0 = 0) (x : RealFock m) :
    split (annOf m φ x) = lift (annOfE φ) (split x) := by
  rw [annOf_eq_sum_excited φ h0, LinearMap.sum_apply]
  rw [map_sum]
  simp only [LinearMap.smul_apply, map_smul]
  conv_rhs => rw [annOfE, lift_sum]
  simp only [lift_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show split (ann m l.1 x) = lift (annC (Excited m) l) (split x) from
    LinearMap.congr_fun (Split_ann_excited l) x]
  first | rfl | exact (Complex.coe_smul (φ l.1) _).symm

/-- **The creation dictionary**: `split ∘ creOf m φ = lift (creOfE φ) ∘ split`
for `φ 0 = 0`. -/
theorem split_creOf (φ : Fin m → ℝ) (h0 : φ 0 = 0) (x : RealFock m) :
    split (creOf m φ x) = lift (creOfE φ) (split x) := by
  rw [creOf_eq_sum_excited φ h0, LinearMap.sum_apply]
  rw [map_sum]
  simp only [LinearMap.smul_apply, map_smul]
  conv_rhs => rw [creOfE, lift_sum]
  simp only [lift_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show split (cre m l.1 x) = lift (creC (Excited m) l) (split x) from
    LinearMap.congr_fun (Split_cre_excited l) x]
  first | rfl | exact (Complex.coe_smul (φ l.1) _).symm

/-! ## 3. Compositions of two superposed modes -/

/-- `split` of `creOf φ ∘ annOf ψ`. -/
theorem split_creOf_annOf (φ ψ : Fin m → ℝ) (hφ : φ 0 = 0) (hψ : ψ 0 = 0)
    (x : RealFock m) :
    split (creOf m φ (annOf m ψ x)) = lift (creOfE φ ∘ₗ annOfE ψ) (split x) := by
  rw [split_creOf φ hφ, split_annOf ψ hψ, lift_comp, LinearMap.comp_apply]

/-- `split` of `annOf φ ∘ creOf ψ`. -/
theorem split_annOf_creOf (φ ψ : Fin m → ℝ) (hφ : φ 0 = 0) (hψ : ψ 0 = 0)
    (x : RealFock m) :
    split (annOf m φ (creOf m ψ x)) = lift (annOfE φ ∘ₗ creOfE ψ) (split x) := by
  rw [split_annOf φ hφ, split_creOf ψ hψ, lift_comp, LinearMap.comp_apply]

/-! ## 4. The condensate coordinate -/

/-- `split` of the condensate creation. -/
theorem split_cre_zero (x : RealFock m) :
    split (cre m 0 x) = a0d (split x) :=
  LinearMap.congr_fun (Split_cre_zero (m := m)) x

/-- `split` of the condensate annihilation. -/
theorem split_ann_zero (x : RealFock m) :
    split (ann m 0 x) = a0 (split x) :=
  LinearMap.congr_fun (Split_ann_zero (m := m)) x

/-- `split` of an excited coordinate annihilation. -/
theorem split_ann_excited (j : Excited m) (x : RealFock m) :
    split (ann m j.1 x) = lift (annC (Excited m) j) (split x) :=
  LinearMap.congr_fun (Split_ann_excited j) x

/-- `split` of an excited coordinate creation. -/
theorem split_cre_excited (j : Excited m) (x : RealFock m) :
    split (cre m j.1 x) = lift (creC (Excited m) j) (split x) :=
  LinearMap.congr_fun (Split_cre_excited j) x

/-! ## 5. Condensate powers and the general sandwich -/

/-- The `p`-fold condensate annihilation `(ann m 0)^p` on the mode lattice. -/
noncomputable def annPow : ℕ → RealFock m →ₗ[ℝ] RealFock m
  | 0 => 1
  | p + 1 => (annPow p).comp (ann m 0)

/-- The `q`-fold condensate creation `(cre m 0)^q` on the mode lattice. -/
noncomputable def crePow : ℕ → RealFock m →ₗ[ℝ] RealFock m
  | 0 => 1
  | q + 1 => (crePow q).comp (cre m 0)

@[simp] lemma annPow_zero : annPow (m := m) 0 = 1 := rfl
@[simp] lemma crePow_zero : crePow (m := m) 0 = 1 := rfl
@[simp] lemma annPow_succ (p : ℕ) : annPow (m := m) (p + 1) = (annPow p).comp (ann m 0) := rfl
@[simp] lemma crePow_succ (q : ℕ) : crePow (m := m) (q + 1) = (crePow q).comp (cre m 0) := rfl

/-- `split` intertwines the condensate powers with `a0pow`. -/
theorem split_annPow : ∀ (p : ℕ) (x : RealFock m),
    split (annPow (m := m) p x) = a0pow p (split x) := by
  intro p
  induction p with
  | zero => intro x; simp
  | succ d ih =>
    intro x
    rw [annPow_succ, LinearMap.comp_apply, ih, split_ann_zero, a0pow_succ,
      LinearMap.comp_apply]

/-- `split` intertwines the condensate powers with `a0dpow`. -/
theorem split_crePow : ∀ (q : ℕ) (x : RealFock m),
    split (crePow (m := m) q x) = a0dpow q (split x) := by
  intro q
  induction q with
  | zero => intro x; simp
  | succ d ih =>
    intro x
    rw [crePow_succ, LinearMap.comp_apply, ih, split_cre_zero, a0dpow_succ,
      LinearMap.comp_apply]

/-- **The general sandwich.**  If the spectator word `W` corresponds to `lift B`, then
`(a₀†)^q ∘ W ∘ (a₀)^p` corresponds to `(a₀†)^q ∘ (lift B) ∘ (a₀)^p`. -/
theorem split_sandwich (p q : ℕ) (B : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (W : RealFock m →ₗ[ℝ] RealFock m) (hW : ∀ y, split (W y) = lift B (split y))
    (x : RealFock m) :
    split (crePow q (W (annPow p x)))
      = ((a0dpow q).comp ((lift B).comp (a0pow p))) (split x) := by
  rw [split_crePow, hW, split_annPow]
  rfl

/-- The anti-normal (monoOp) form of the sandwich, via the Wick expansion
`Work.BoseB4.a0dpow_comp_lift_comp_a0pow`. -/
theorem split_sandwich_mono (p q : ℕ) (B : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (W : RealFock m →ₗ[ℝ] RealFock m) (hW : ∀ y, split (W y) = lift B (split y))
    (x : RealFock m) :
    split (crePow q (W (annPow p x)))
      = (∑ k ∈ Finset.range (p + 1),
          (((-1 : ℂ) ^ k) * ((k.factorial : ℕ) : ℂ) * ((p.choose k : ℕ) : ℂ)
              * ((q.choose k : ℕ) : ℂ)) • monoOp (p - k) (q - k) B) (split x) := by
  rw [split_sandwich p q B W hW x, a0dpow_comp_lift_comp_a0pow]

/-- `crePow 1` is the condensate creation. -/
theorem crePow_one : crePow (m := m) 1 = cre m 0 := by
  rw [crePow_succ, crePow_zero]
  ext x; simp

/-- `annPow 1` is the condensate annihilation. -/
theorem annPow_one : annPow (m := m) 1 = ann m 0 := by
  rw [annPow_succ, annPow_zero]
  ext x; simp

/-- `lift` of the identity is the identity. -/
@[simp] lemma lift_one : lift (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)) = 1 := by
  ext x n
  simp [lift_apply]

/-! ## 6. Row templates -/

/-- **The kinetic-type row** (`Σ_k c_k a_k†a_k` with superposed modes): transport of a
weighted sum of `creOf φ_k ∘ annOf φ_k`. -/
theorem split_weighted_number {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (s : Finset Mode) (c : Mode → ℝ) (φ : Mode → Fin m → ℝ)
    (hφ : ∀ k ∈ s, φ k 0 = 0) (x : RealFock m) :
    split ((∑ k ∈ s, c k • ((creOf m (φ k)).comp (annOf m (φ k)))) x)
      = (monoOp 0 0 (∑ k ∈ s, ((c k : ℝ) : ℂ) •
          ((creOfE (φ k)).comp (annOfE (φ k))))) (split x) := by
  have h1 : (∑ k ∈ s, c k • ((creOf m (φ k)).comp (annOf m (φ k)))) x
      = ∑ k ∈ s, c k • ((creOf m (φ k)).comp (annOf m (φ k)) x) := by
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [LinearMap.smul_apply]
  rw [h1, map_sum]
  have h2 : ∀ k ∈ s, split (c k • ((creOf m (φ k)).comp (annOf m (φ k)) x))
      = c k • lift ((creOfE (φ k)).comp (annOfE (φ k))) (split x) := by
    intro k hk
    rw [map_smul, LinearMap.comp_apply, split_creOf_annOf _ _ (hφ k hk) (hφ k hk)]
  rw [Finset.sum_congr rfl h2, monoOp_zero_zero, lift_sum]
  simp only [lift_smul, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.smul_apply]
  exact (Complex.coe_smul (c k) (lift ((creOfE (φ k)).comp (annOfE (φ k))) (split x))).symm

/-- **The number-type row** (`Σ_{l≠0} w_l a_l†a_l` on coordinate modes). -/
theorem split_excited_number (w : Fin m → ℝ) (x : RealFock m) :
    split ((∑ l : Excited m, w l.1 • ((cre m l.1).comp (ann m l.1))) x)
      = (monoOp 0 0 (∑ l : Excited m, ((w l.1 : ℝ) : ℂ) •
          ((creC (Excited m) l).comp (annC (Excited m) l)))) (split x) := by
  have h1 : (∑ l : Excited m, w l.1 • ((cre m l.1).comp (ann m l.1))) x
      = ∑ l : Excited m, w l.1 • (((cre m l.1).comp (ann m l.1)) x) := by
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [LinearMap.smul_apply]
  rw [h1, map_sum]
  have h2 : ∀ l : Excited m, split (w l.1 • (((cre m l.1).comp (ann m l.1)) x))
      = w l.1 • lift ((creC (Excited m) l).comp (annC (Excited m) l)) (split x) := by
    intro l
    rw [map_smul, LinearMap.comp_apply, split_cre_excited, split_ann_excited, lift_comp,
      LinearMap.comp_apply]
  rw [Finset.sum_congr rfl fun l _ => h2 l, monoOp_zero_zero, lift_sum]
  simp only [lift_smul, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [LinearMap.smul_apply]
  exact (Complex.coe_smul (w l.1)
    (lift ((creC (Excited m) l).comp (annC (Excited m) l)) (split x))).symm

/-- The sandwich with the trivial spectator word `W = 1`. -/
theorem split_identity_sandwich (p q : ℕ) (x : RealFock m) :
    split (crePow q (annPow p x))
      = ((a0dpow q).comp
          ((lift (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))).comp (a0pow p)))
        (split x) := by
  have h := split_sandwich p q (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (LinearMap.id : RealFock m →ₗ[ℝ] RealFock m) (by intro y; rw [lift_one]; rfl) x
  simpa using h

/-- **The contact row** `(a₀†)²a₀²` (row 4 of the dictionary), in sandwich form. -/
theorem split_contact (c : ℝ) (x : RealFock m) :
    split (c • (crePow 2 (annPow 2 x)))
      = (c • ((a0dpow 2).comp
          ((lift (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))).comp (a0pow 2))))
        (split x) := by
  rw [map_smul, split_identity_sandwich, LinearMap.smul_apply]

/-- **The chemical-potential row** `n₀` (row 5 of the dictionary), in sandwich form. -/
theorem split_n0 (c : ℝ) (x : RealFock m) :
    split (c • (crePow 1 (annPow 1 x)))
      = (c • ((a0dpow 1).comp
          ((lift (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))).comp (a0pow 1))))
        (split x) := by
  rw [map_smul, split_identity_sandwich, LinearMap.smul_apply]

/-- One-sided sandwich: `W` followed by `(a₀)^p` (the adjoint half of the pairing row). -/
theorem split_spectator_annPow (p : ℕ) (B : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (W : RealFock m →ₗ[ℝ] RealFock m) (hW : ∀ y, split (W y) = lift B (split y))
    (x : RealFock m) :
    split (W (annPow p x)) = ((lift B).comp (a0pow p)) (split x) := by
  rw [hW, split_annPow]
  rfl

/-- One-sided sandwich: `(a₀†)^q` followed by `W`. -/
theorem split_crePow_spectator (q : ℕ) (B : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (W : RealFock m →ₗ[ℝ] RealFock m) (hW : ∀ y, split (W y) = lift B (split y))
    (x : RealFock m) :
    split (crePow q (W x)) = ((a0dpow q).comp (lift B)) (split x) := by
  rw [split_crePow, hW]
  rfl

/-- The `n₀ ∘ W` row (`W` a spectator word) reduces to the sandwich
`Work.BoseBoxFock.split_sandwiches` with `p = q = 1` (the identity
`a0d ∘ lift B ∘ a0 = monoOp 1 1 B − monoOp 0 0 B` is proved there); recorded here as
the two-step reduction for reuse. -/
theorem split_n0_spectator_reduce (B : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (W : RealFock m →ₗ[ℝ] RealFock m) (hW : ∀ y, split (W y) = lift B (split y))
    (x : RealFock m) :
    split ((cre m 0).comp ((ann m 0).comp W) x)
      = ((a0d.comp a0).comp (lift B)) (split x) := by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, split_cre_zero, split_ann_zero, hW]
  rfl


/-! ## 8. The `a₀† ∘ W ∘ a₀` and `n₀ ∘ W` rows with a general spectator word -/

/-- `1.comp f = f` for endomorphisms of a `ℂ`-vector space. -/
lemma one_comp_self {E : Type*} [AddCommGroup E] [Module ℂ E] (f : E →ₗ[ℂ] E) :
    (1 : E →ₗ[ℂ] E).comp f = f := by
  ext x
  rw [LinearMap.comp_apply, Module.End.one_apply]

/-- `f.comp 1 = f`. -/
lemma comp_one_self {E : Type*} [AddCommGroup E] [Module ℂ E] (f : E →ₗ[ℂ] E) :
    f.comp (1 : E →ₗ[ℂ] E) = f := by
  ext x
  rw [LinearMap.comp_apply, Module.End.one_apply]

/-- The CCR at the vector level: `a₀ (a₀† z) = a₀† (a₀ z) + z`. -/
lemma a0_a0d_apply (z : FockCore (cfock (Excited m))) :
    a0 (a0d z) = a0d (a0 z) + z := by
  have h := LinearMap.congr_fun (ccr (E := cfock (Excited m))) z
  simpa [LinearMap.comp_apply] using h

/-- **The condensate sandwich with a general spectator word**:
`a₀† ∘ (lift B) ∘ a₀ = monoOp 1 1 B − monoOp 0 0 B` (FS `eq:subst-z`'s row
`a₀†a₀ ↦ |z|² − 1`). -/
theorem a0d_lift_a0 (B : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)) :
    a0d.comp ((lift B).comp a0) = (monoOp 1 1 B - monoOp 0 0 B) := by
  have hmain : a0d.comp ((lift B).comp a0) = (a0.comp (a0d.comp (lift B))) - lift B := by
    refine LinearMap.ext fun y => ?_
    rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.comp_apply, LinearMap.comp_apply,
      show (lift B) (a0 y) = a0 ((lift B) y) from LinearMap.congr_fun (lift_comm_a0 B) y]
    exact (eq_sub_iff_add_eq).mpr (a0_a0d_apply (lift B y)).symm
  have h1 : a0.comp (a0d.comp (lift B)) = monoOp 1 1 B := by
    rw [monoOp, a0pow_succ, a0pow_zero, a0dpow_succ, a0dpow_zero, one_comp_self,
      one_comp_self]
  have h2 : monoOp 0 0 B = lift B := monoOp_zero_zero B
  rw [hmain, h1, h2]

/-- **The row `a₀† ∘ W ∘ a₀`** for an arbitrary spectator word `W` (row 6 of the
dictionary, and the `Q̃₃` row's shape). -/
theorem split_a0d_spectator_a0 (B : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (W : RealFock m →ₗ[ℝ] RealFock m) (hW : ∀ y, split (W y) = lift B (split y))
    (x : RealFock m) :
    split ((cre m 0).comp (W.comp (ann m 0)) x)
      = (monoOp 1 1 B - monoOp 0 0 B) (split x) := by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, split_cre_zero, hW, split_ann_zero]
  exact LinearMap.congr_fun (a0d_lift_a0 B) (split x)

/-- **The row `n₀ ∘ W`** for an arbitrary spectator word `W` (row 10 of the
dictionary). -/
theorem split_n0_spectator (B : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (W : RealFock m →ₗ[ℝ] RealFock m) (hW : ∀ y, split (W y) = lift B (split y))
    (x : RealFock m) :
    split ((cre m 0).comp ((ann m 0).comp W) x)
      = (monoOp 1 1 B - monoOp 0 0 B) (split x) := by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, split_cre_zero, split_ann_zero, hW]
  rw [show a0 (lift B (split x)) = (lift B) (a0 (split x)) from
    (LinearMap.congr_fun (lift_comm_a0 B) (split x)).symm]
  exact LinearMap.congr_fun (a0d_lift_a0 B) (split x)


/-! ## 9. The assembly engine: the `c`-number substitution with a pointwise floor -/

/-- `bomb Ψ (W Ψ)` is the real part of the ℓ² expectation of the transported word. -/
theorem bomb_eq_of_transport {ι : Type*} (s : Finset ι) (p q : ι → ℕ)
    (B : ι → cfock (Excited m) →ₗ[ℂ] cfock (Excited m)) (W : RealFock m →ₗ[ℝ] RealFock m)
    (hW : ∀ x, split (W x) = (∑ i ∈ s, monoOp (p i) (q i) (B i)) (split x)) (Ψ : RealFock m) :
    bomb m Ψ (W Ψ) = (inner ℂ (Embed (cfock (Excited m)) (split Ψ))
      (Embed (cfock (Excited m))
        (∑ i ∈ s, monoOp (p i) (q i) (B i) (split Ψ)))).re := by
  have hcore : coreInner (split Ψ) ((∑ i ∈ s, monoOp (p i) (q i) (B i)) (split Ψ))
      = ((bomb m Ψ (W Ψ) : ℝ) : ℂ) := by
    rw [← hW Ψ, Split_inner]
  have hbomb : (coreInner (split Ψ) ((∑ i ∈ s, monoOp (p i) (q i) (B i)) (split Ψ))).re
      = bomb m Ψ (W Ψ) := by
    rw [hcore]; simp
  rw [← hbomb, coreInner, LinearMap.sum_apply]

/-- **The `c`-number substitution with a pointwise floor, on the mode lattice**
(FS `thm:Kafz`'s `eq:IntroK(z)`, with the floor supplied as a hypothesis). -/
theorem kafz_lattice_pointwise {ι : Type*} (s : Finset ι) (p q : ι → ℕ)
    (B : ι → cfock (Excited m) →ₗ[ℂ] cfock (Excited m)) (W : RealFock m →ₗ[ℝ] RealFock m)
    (hW : ∀ x, split (W x) = (∑ i ∈ s, monoOp (p i) (q i) (B i)) (split x))
    (c : ℝ) (Ψ : RealFock m)
    (h : ∀ z : ℂ, c * ‖Phi (split Ψ) z‖ ^ 2 ≤
      (∑ i ∈ s, z ^ (p i) * (starRingEnd ℂ z) ^ (q i) *
        inner ℂ (Phi (split Ψ) z) (B i (Phi (split Ψ) z))).re) :
    c * bomb m Ψ Ψ ≤ bomb m Ψ (W Ψ) := by
  have hbomb := bomb_eq_of_transport s p q B W hW Ψ
  have hnorm : ‖Embed (cfock (Excited m)) (split Ψ)‖ ^ 2 = bomb m Ψ Ψ :=
    (bomb_self_eq_norm_split Ψ).symm
  have hmain := Kafz_lower_bound_pointwise (E := cfock (Excited m)) s p q B c (split Ψ) h
  rw [hnorm] at hmain
  rw [hbomb]
  exact hmain

/-- **`model_kafz` from the dictionary and the pointwise floor.**  If the honest model
`H2ndHon` transports under `split` to the anti-normal family `(p, q, B)`, and the
anti-Wick symbol of that family dominates `⨅_ρ valFS ρ − errKafz` pointwise at
`Phi (split Ψ) z`, then `model_kafz`'s inequality holds at `Ψ`.  This reduces
`model_kafz` to (i) the dictionary `hW` (see the row tables) and (ii) the pointwise
floor (the symbol comparison of `KAFZ_HONEST_ROUTE.md` §1.3). -/
theorem model_kafz_of_floor {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, HonestModes v μ} {μ R C : ℝ} {n : ℕ}
    {Ψ : RealFock (HM μ).m} {ι : Type*} (s : Finset ι) (p q : ι → ℕ)
    (B : ι → cfock (Excited (HM μ).m) →ₗ[ℂ] cfock (Excited (HM μ).m))
    (hW : ∀ x, split (H2ndHon v h fc fu HM μ x)
        = (∑ i ∈ s, monoOp (p i) (q i) (B i)) (split x))
    (hfloor : ∀ z : ℂ,
      ((⨅ (ρ : {ρ : ℝ // 0 ≤ ρ}), (HonestBoxFam v h fc fu HM μ).valFS ρ.1)
          - Work.BoseFixR.errKafz v R μ C) * ‖Phi (split Ψ) z‖ ^ 2 ≤
      (∑ i ∈ s, z ^ (p i) * (starRingEnd ℂ z) ^ (q i) *
        inner ℂ (Phi (split Ψ) z) (B i (Phi (split Ψ) z))).re) :
    ((⨅ (ρ : {ρ : ℝ // 0 ≤ ρ}), (HonestBoxFam v h fc fu HM μ).valFS ρ.1)
        - Work.BoseFixR.errKafz v R μ C) * bomb (HM μ).m Ψ Ψ
      ≤ bomb (HM μ).m Ψ (H2ndHon v h fc fu HM μ Ψ) :=
  kafz_lattice_pointwise s p q B _ hW _ Ψ hfloor


/-! ## 10. The gap row `N − n₀` -/

/-- `totNumOp m − n₀` is the number operator of the excited coordinates. -/
theorem totNumOp_sub_n0 :
    totNumOp (m := m) - n0 = ∑ l : Excited m, ((cre m l.1).comp (ann m l.1)) := by
  have h := sum_univ_eq_zero_add (fun i : Fin m => (cre m i).comp (ann m i))
  rw [totNumOp, n0]
  simp only [modeNumOp]
  rw [h]
  abel

/-- **The gap row** `(b/2ℓ²)(N − n₀)`. -/
theorem split_gap (c : ℝ) (x : RealFock m) :
    split (c • ((totNumOp m - n0 : RealFock m →ₗ[ℝ] RealFock m) x))
      = (c • monoOp 0 0 (∑ l : Excited m, (1 : ℂ) •
          ((creC (Excited m) l).comp (annC (Excited m) l)))) (split x) := by
  rw [totNumOp_sub_n0, map_smul, LinearMap.smul_apply]
  have h := split_excited_number (m := m) (fun _ => (1 : ℝ)) x
  simp only [one_smul, Complex.ofReal_one] at h
  rw [h]
  simp only [one_smul]


/-! ## 11. `valFS` as an infimum: the window Rayleigh quotient dominates it

**Warning / new obligation.**  `KzValFS` is an `⨅` over the window, and in `ℝ` the
lemma `ciInf_le` needs `BddBelow (range …)`: `⨅` of a set unbounded below is the junk
value `0`, so `valFS ρ ≤ rayleigh` is *not* free.  The missing input

    ∀ ρ : ℝ, 0 ≤ ρ → BddBelow (range (fun g : window, g ≠ 0 => ⟪g, KzOpFS ρ g⟫/⟪g,g⟫))

is FS's `lem:Roughbounds` in its crudest form ("the substituted operator is bounded
below on the window by some `−K(ρ)`, uniformly in the state").  It is needed twice:
for the pointwise floor (F2) *and* for the statement's own truth (as stated, if the
range were unbounded below at some honest datum, `⨅_ρ valFS ρ` would be the junk `0`
and the inequality would fail).  It is *not* the sharp §9–11 analysis: any explicit
lower bound works, and it follows from FS's `lem:Roughbounds` or from expanding
`KzOpFS ρ` and bounding each row by AM–GM with the window `⟨n₊⟩ ≤ 𝓜` (the c-number's
`½ρ²ℓ³Ŵ₁ω(0)` dominates the `ρ`-linear rows for large `ρ`). -/

/-- **`valFS ρ` is below any window Rayleigh quotient** (the step (F2) of the route),
*conditional* on the lower-boundedness of the window Rayleigh quotients. -/
theorem valFS_le_rayleigh {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (D : Work.BoseFixR.KzDatum) (ρ : ℝ) (f : D.F.H)
    (hbd : BddBelow (Set.range (fun g : {g : D.F.H // D.T.NWindow D.E.bigM g ∧ g ≠ 0} =>
      D.F.qw g.1 (KzOpFS D.F D.T D.E D.gHat0 ρ) / D.F.normSq g.1)))
    (hwin : D.T.NWindow D.E.bigM f) (hf : f ≠ 0) :
    D.valFS ρ ≤ D.F.qw f (KzOpFS D.F D.T D.E D.gHat0 ρ) / D.F.normSq f := by
  rw [Work.BoseFixR.KzDatum.valFS, KzValFS]
  exact ciInf_le hbd ⟨f, hwin, hf⟩

end Work.BoseBoxFock
