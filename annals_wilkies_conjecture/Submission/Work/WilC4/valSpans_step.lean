/-
  `valSpans_step`: the value-spanning relation is compatible with composition,

    `ValSpans S T r` and `ValSpans T V 1`  ⟹  `ValSpans S V (r + 1)`.

  In value-group language (`ν x` the Archimedean value, `Γ S = {ν c : c ∈ S}`): if the values
  of the elements of `T` lie in `⟨ν x_1, …, ν x_r⟩_ℚ + Γ S` and the values of the elements of
  `V` lie in `⟨ν δ⟩_ℚ + Γ T`, then the values of the elements of `V` lie in
  `⟨ν x_1, …, ν x_r, ν δ⟩_ℚ + Γ S`.  The definition `ValSpans` keeps the denominators of this
  rational-linear combination explicit, so the proof below just has to *combine* the two
  certificates: raising the `V`-certificate to the `N₁`-th power and substituting the
  `T`-certificate for `c₂^{N₁}` turns the two unit certificates into one, and the concrete
  field identity relating the two expressions is `step_algebra_id`.

  The element `c₂ ∈ T` that the `V`-certificate produces is *itself* an element of `T`, so it is
  fed back into the `T`-certificate; this is where the hypothesis `ValSpans S T r` is used.
-/
import Mathlib
import Submission.Work.WilC4.Defs

set_option autoImplicit false
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilC4

/-! ## Arithmetic of `IsUnitVal` (local, so that the proof below is self-contained) -/

private lemma isUnitVal_one {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] :
    IsUnitVal (1 : M) := by
  refine ⟨1, ?_, ?_⟩ <;> (rw [abs_one]; norm_num)

private lemma isUnitVal_mul {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    {x y : M} (hx : IsUnitVal x) (hy : IsUnitVal y) : IsUnitVal (x * y) := by
  obtain ⟨N, hN1, hN2⟩ := hx
  obtain ⟨K, hK1, hK2⟩ := hy
  have hcast : ((N * K + N + K : ℕ) : M) + 1 = ((N : M) + 1) * ((K : M) + 1) := by
    push_cast; ring
  refine ⟨N * K + N + K, ?_, ?_⟩
  · rw [abs_mul, hcast, mul_inv]
    exact mul_le_mul hN1 hK1 (by positivity) (abs_nonneg x)
  · rw [abs_mul, hcast]
    exact mul_le_mul hN2 hK2 (abs_nonneg y) (by positivity)

private lemma isUnitVal_inv {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    {x : M} (hx : IsUnitVal x) : IsUnitVal x⁻¹ := by
  obtain ⟨N, h1, h2⟩ := hx
  have hxpos : 0 < |x| := lt_of_lt_of_le (by positivity) h1
  refine ⟨N, ?_, ?_⟩
  · rw [abs_inv]
    exact (inv_le_inv₀ (by positivity) hxpos).mpr h2
  · rw [abs_inv]
    exact inv_le_of_inv_le₀ (by positivity) h1

private lemma isUnitVal_pow {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    {x : M} (hx : IsUnitVal x) : ∀ k : ℕ, IsUnitVal (x ^ k)
  | 0 => by simpa using isUnitVal_one
  | k + 1 => by rw [pow_succ]; exact isUnitVal_mul (isUnitVal_pow hx k) hx

/-- `ValEq` is reflexive (take `N = 1`). -/
private lemma valEq_refl {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    (x : M) : ValEq x x := by
  refine ⟨1, by norm_num, ?_, ?_⟩ <;> simp

/-- Splitting off the first factor of an integer monomial in `Fin (r+1)`. -/
private lemma zmono_cons {M : Type} [Field M] {r : ℕ} (x : Fin r → M) (δ : Fin 1 → M)
    (q₁ : Fin r → ℤ) (q₂ : Fin 1 → ℤ) (N₁ : ℕ) :
    zmono (Fin.cons (δ 0) x) (Fin.cons (q₂ 0 * N₁) (fun i => -q₁ i))
      = (zmono δ q₂) ^ N₁ * (zmono x q₁)⁻¹ := by
  unfold zmono
  rw [Fin.prod_univ_succ, Fin.prod_univ_one]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [Finset.prod_congr rfl (fun i _ => zpow_neg (x i) (q₁ i)), Finset.prod_inv_distrib]
  rw [zpow_mul, zpow_natCast]

/-- The field identity behind the combination of the two certificates:
`a⁻¹ y^{N₂N₁} / (D^{N₁} W⁻¹) = (b y^{N₂}/D)^{N₁} · (a b^{N₁}/W)⁻¹` for `b ≠ 0`.

(`b ≠ 0` is exactly what the `V`-certificate supplies, via its base element `c₂ ∈ T \ {0}`;
without it the identity fails when `b = 0` and `N₁ > 0`, and every certificate here does carry
a nonzero base element.) -/
private lemma step_algebra_id {M : Type} [Field M] {a b y D W : M} {N₁ N₂ : ℕ}
    (hb : b ≠ 0) :
    a⁻¹ * y ^ (N₂ * N₁) / (D ^ N₁ * W⁻¹)
      = (b * y ^ N₂ / D) ^ N₁ * (a * b ^ N₁ / W)⁻¹ := by
  have hb' : b ^ N₁ ≠ 0 := pow_ne_zero _ hb
  field_simp
  ring

set_option linter.unusedVariables false in
theorem valSpans_step {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    {S T V : Set M} {r : ℕ} (hS : IsValBase S) (hT : IsValBase T) (h1 : ValSpans S T r)
    (h2 : ValSpans T V 1) : ValSpans S V (r + 1) := by
  -- the `r` generators spanning the values of `T` over `Γ S`
  obtain ⟨x, hx⟩ := h1
  -- the single generator spanning the values of `V` over `Γ T`
  obtain ⟨δ, hδ⟩ := h2
  -- the `r + 1` generators for `V` over `Γ S`: the old ones together with `δ 0`
  refine ⟨Fin.cons (δ 0) x, ?_⟩
  intro y hy hValOf
  -- certificate for `y` over `Γ T`
  obtain ⟨N₂, hN₂, q₂, c₂, hc₂T, hc₂0, hu₂⟩ := hδ y hy hValOf
  -- `c₂ ∈ T \ {0}` has a value in `T`, so it has a certificate over `Γ S`
  have hValT : ValOf T c₂ := ⟨c₂, hc₂T, hc₂0, valEq_refl c₂⟩
  obtain ⟨N₁, hN₁, q₁, c₁, hc₁S, hc₁0, hu₁⟩ := hx c₂ hc₂0 hValT
  -- combine: exponent `N₂ · N₁`, generators `(δ 0, x)`, base element `c₁⁻¹ ∈ S`
  refine ⟨N₂ * N₁, Nat.mul_ne_zero hN₂ hN₁, Fin.cons (q₂ 0 * N₁) (fun i => -q₁ i),
    c₁⁻¹, hS.2.1 c₁ hc₁S hc₁0, inv_ne_zero hc₁0, ?_⟩
  rw [zmono_cons]
  rw [step_algebra_id (b := c₂) hc₂0]
  exact isUnitVal_mul (isUnitVal_pow hu₂ N₁) (isUnitVal_inv hu₁)

end Work.WilC4
