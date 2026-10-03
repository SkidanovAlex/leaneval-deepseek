import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ArcNumOrth

/-!
# (A3) The frequency-side (Fourier) step: supports of convolutions and the vanishing integral

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066,
Lemma `ortho`(ii)(iii) (§4) — the sentence *"From inspecting the Fourier transform, it suffices to
show that …"*.

The major-arc systems of the Ionescu–Wainger theorem live on the Fourier side: a function
`f_α ∈ ℓ²(ℤ)` with Fourier support in the arc `α + [-ε,ε]` corresponds to its Fourier transform
`F_α`, an `L²`-function on the circle supported in that arc.  Under this correspondence

* the pointwise product of two `ℤ`-functions has Fourier transform the **convolution** of their
  transforms, so the pairing `Σ_n f(n) conj(g(n))` (Parseval) of a product becomes the integral of
  the product of the convolved transforms;
* the **support of a convolution** is contained in the Minkowski sum `E + D` of the supports;
* hence the pairing vanishes as soon as the Minkowski sums of the two families of arcs are
  **disjoint** — and that disjointness is exactly the arithmetic content of `Σ_{j≤r}(α_j+θ_j) ≠
  Σ_{j>r}(α_j+θ_j)` proved in `ArcSep.lean` / `ArcNumOrth.lean`.

This file supplies the elementary analytic part: the convolution on the circle `𝕋 = ℝ/ℤ`, the
support of an `n`-fold convolution, and the vanishing of `∫ (✻_i F_i) conj (✻_i G_i)` when the
Minkowski sums of the two families of arcs are disjoint.  The first section also identifies the
Minkowski sums of *arcs* with the set of signed sums appearing in Tao's argument.
-/

open Finset MeasureTheory
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-! ## Arcs and their Minkowski sums -/

/-- The closed arc `α + [-ε,ε]` around `α` in the circle `𝕋 = ℝ/ℤ`. -/
def arcSet (α : Circle) (ε : ℝ) : Set Circle := {ξ | ∃ θ : ℝ, |θ| ≤ ε ∧ ξ = α + (θ : Circle)}

/-- The Minkowski sum of two subsets of a commutative additive monoid. -/
def setAdd {G : Type*} [Add G] (E D : Set G) : Set G := {ξ | ∃ a ∈ E, ∃ b ∈ D, a + b = ξ}

/-- The Minkowski sum `E 0 + E 1 + ⋯ + E (n-1)` of a `Fin n`-indexed family of subsets of a
commutative additive monoid, as the set of sums `Σ i, f i` with `f i ∈ E i`. -/
def setSumFin {G : Type*} [AddCommMonoid G] (n : ℕ) (E : Fin n → Set G) : Set G :=
  {x | ∃ f : Fin n → G, (∀ i, f i ∈ E i) ∧ ∑ i, f i = x}

/-- The Minkowski sum of the arcs `α i + [-ε,ε]` is exactly the set of the sums
`Σ i, (α i + θ i)` with `|θ i| ≤ ε`. -/
lemma mem_setSumFin_arcSet {n : ℕ} {α : Fin n → Circle} {ε : ℝ} {ξ : Circle} :
    ξ ∈ setSumFin n (fun i => arcSet (α i) ε) ↔
      ∃ θ : Fin n → ℝ, (∀ i, |θ i| ≤ ε) ∧ ∑ i, (α i + (θ i : Circle)) = ξ := by
  constructor
  · rintro ⟨f, hf, hsum⟩
    choose θ hθ hf' using hf
    exact ⟨θ, hθ, by rw [← hsum]; exact Finset.sum_congr rfl fun i _ => (hf' i).symm⟩
  · rintro ⟨θ, hθ, hsum⟩
    exact ⟨fun i => α i + (θ i : Circle), fun i => ⟨θ i, hθ i, rfl⟩, hsum⟩

/-! ## The convolution on the circle and the support of a convolution -/

/-- The convolution of two functions on the circle with respect to the probability Haar measure. -/
noncomputable def circConv (F G : Circle → ℂ) : Circle → ℂ :=
  fun ξ => ∫ η, F η * G (ξ - η) ∂AddCircle.haarAddCircle

/-- **Support of a convolution**: if `F` vanishes off `E` and `G` vanishes off `D`, then the
convolution `F * G` vanishes off the Minkowski sum `E + D`. -/
lemma circConv_eq_zero_of_notMem_setAdd {E D : Set Circle} {F G : Circle → ℂ}
    (hF : ∀ ξ, ξ ∉ E → F ξ = 0) (hG : ∀ ξ, ξ ∉ D → G ξ = 0) :
    ∀ ξ, ξ ∉ setAdd E D → circConv F G ξ = 0 := by
  intro ξ hξ
  have h : (fun η => F η * G (ξ - η)) = fun _ => (0 : ℂ) := by
    funext η
    by_cases h1 : η ∈ E
    · have h2 : ξ - η ∉ D := fun h2 => hξ ⟨η, h1, ξ - η, h2, add_sub_cancel η ξ⟩
      rw [hG (ξ - η) h2, mul_zero]
    · rw [hF η h1, zero_mul]
  simp only [circConv, h, integral_zero]

/-! ## The `n`-fold convolution -/

/-- The `n`-fold convolution `✻_{i : Fin n} F i` of a `Fin n`-indexed family of functions on the
circle (the empty convolution is the constant `1`). -/
noncomputable def circConvFin : (n : ℕ) → (Fin n → Circle → ℂ) → Circle → ℂ
  | 0, _ => fun _ => 1
  | 1, F => F 0
  | n + 2, F =>
      circConv (circConvFin (n + 1) (fun i : Fin (n + 1) => F i.castSucc)) (F (Fin.last (n + 1)))

/-- **The support of an `n`-fold convolution** (`n ≥ 1`): it is contained in the Minkowski sum
`Σ i, E i` of the supports. -/
lemma circConvFin_succ_eq_zero_of_notMem_setSumFin :
    ∀ (n : ℕ) {E : Fin (n + 1) → Set Circle} {F : Fin (n + 1) → Circle → ℂ},
      (∀ i, ∀ ξ, ξ ∉ E i → F i ξ = 0) →
        ∀ ξ, ξ ∉ setSumFin (n + 1) E → circConvFin (n + 1) F ξ = 0
  | 0, E, F, hF, ξ, hξ => by
      have h : circConvFin (0 + 1) F = F 0 := rfl
      rw [h]
      refine hF 0 ξ fun hmem => hξ ?_
      exact ⟨fun _ => ξ, fun i => by fin_cases i; exact hmem, by simp⟩
  | k + 1, E, F, hF, ξ, hξ => by
      have h : circConvFin (k + 1 + 1) F =
          circConv (circConvFin (k + 1) (fun i : Fin (k + 1) => F i.castSucc))
            (F (Fin.last (k + 1))) := rfl
      rw [h]
      refine circConv_eq_zero_of_notMem_setAdd
        (E := setSumFin (k + 1) (fun i : Fin (k + 1) => E i.castSucc))
        (D := E (Fin.last (k + 1))) ?_ (hF (Fin.last (k + 1))) ξ ?_
      · intro η hη
        exact circConvFin_succ_eq_zero_of_notMem_setSumFin k (E := fun i => E i.castSucc)
          (F := fun i => F i.castSucc) (fun i => hF i.castSucc) η hη
      · rintro ⟨a, ⟨f, hf, hfa⟩, b, hb, hab⟩
        refine hξ ⟨Fin.snoc f b, fun i => ?_, ?_⟩
        · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
          · simpa using hf j
          · simpa using hb
        · rw [Fin.sum_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.snoc_last, hfa]
          exact hab

/-! ## The vanishing of the pairing of two convolved families -/

/-- **The vanishing of the pairing of two convolved families whose arc sums are disjoint.**  If the
`F i` are supported in the arcs `E i`, the `G i` in the arcs `D i`, and the Minkowski sums
`Σ_i E i` and `Σ_i D i` are disjoint, then `∫ (✻_i F i) · conj (✻_i G i) = 0` on the circle.

This is the analytic content of Tao's `ortho`(ii)/(iii) "inspect the Fourier transform" step:
the integrand vanishes pointwise because its two factors are supported in disjoint sets. -/
theorem integral_circConvFin_mul_conj_eq_zero {n : ℕ} {E D : Fin (n + 1) → Set Circle}
    {F G : Fin (n + 1) → Circle → ℂ} (hF : ∀ i, ∀ ξ, ξ ∉ E i → F i ξ = 0)
    (hG : ∀ i, ∀ ξ, ξ ∉ D i → G i ξ = 0)
    (hdisj : Disjoint (setSumFin (n + 1) E) (setSumFin (n + 1) D)) :
    ∫ ξ, circConvFin (n + 1) F ξ * star (circConvFin (n + 1) G ξ) ∂AddCircle.haarAddCircle
      = 0 := by
  have hF' := circConvFin_succ_eq_zero_of_notMem_setSumFin n hF
  have hG' := circConvFin_succ_eq_zero_of_notMem_setSumFin n hG
  have h : (fun ξ => circConvFin (n + 1) F ξ * star (circConvFin (n + 1) G ξ)) =
      fun _ => (0 : ℂ) := by
    funext ξ
    by_cases h1 : ξ ∈ setSumFin (n + 1) E
    · have h2 : ξ ∉ setSumFin (n + 1) D := fun h2 => (Set.disjoint_left.mp hdisj h1) h2
      rw [hG' ξ h2, star_zero, mul_zero]
    · rw [hF' ξ h1, zero_mul]
  simp only [h, integral_zero]

/-! ## From the arithmetic to the disjointness of the arc sums -/

/-- **Tao's `ortho`(iii), reduced to its arithmetic core.**  For a sunflower with core `A₀` (whose
petals are the pairwise disjoint sets `P i`) and two tuples `α, β` of points of exact denominators
`Q_{P i}` which differ in at least one coordinate, the Minkowski sums of the arcs
`α i + [-ε,ε]` and `β i + [-ε,ε]` are disjoint, under the smallness condition
`2 · #ι · ε < 1/∏_i Q_{P i}`.

Combined with `integral_circConvFin_mul_conj_eq_zero`, this gives the vanishing of the pairing
`∫ (✻_i F_i) · conj (✻_i G_i)` for the two halves of the tuple. -/
theorem disjoint_setSumFin_arcSet_of_petal {n : ℕ} {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {P : Fin (n + 1) → Finset ℕ} (hP : ∀ i, P i ⊆ S)
    (hdisj : ∀ i j : Fin (n + 1), i ≠ j → Disjoint (P i) (P j))
    {α β : Fin (n + 1) → Circle} (hα : ∀ i, α i ∈ sigmaA (P i)) (hβ : ∀ i, β i ∈ sigmaA (P i))
    (hne : ∃ i, α i ≠ β i) {ε : ℝ}
    (hsmall : 2 * ((n + 1 : ℕ) : ℝ) * ε < 1 / ((∏ i, QA (P i) : ℕ) : ℝ)) :
    Disjoint (setSumFin (n + 1) (fun i => arcSet (α i) ε))
      (setSumFin (n + 1) (fun i => arcSet (β i) ε)) := by
  rw [Set.disjoint_left]
  intro ξ h1 h2'
  rw [mem_setSumFin_arcSet] at h1 h2'
  obtain ⟨θ, hθ, hsum1⟩ := h1
  obtain ⟨θ', hθ', hsum2⟩ := h2'
  refine sigmaA_petal_sum_perturbed_ne_zero h2 hS hP hdisj hα hβ hne hθ hθ'
    (by simpa using hsmall) ?_
  rw [Finset.sum_sub_distrib, hsum1, hsum2, sub_self]

/-- **Tao's `ortho`(ii), reduced to its arithmetic core (`HasNonce` form).**  For a family
`A : Fin r ⊕ Fin r → Finset ℕ` of subsets of a pairwise coprime `S` carrying a nonce, and points
`α i ∈ Σ_{A (inl i)}`, `β i ∈ Σ_{A (inr i)}` of exact denominators, the Minkowski sums of the arcs
`α i + [-ε,ε]` and `β i + [-ε,ε]` are disjoint, under the smallness condition
`2r ε < 1/∏_j Q_{A j}`.

Combined with `integral_circConvFin_mul_conj_eq_zero` this is the analytic step of Tao's denominator
orthogonality: the pairing `∫ (✻_i F_i) · conj (✻_i G_i)` of the two halves of the tuple vanishes. -/
theorem disjoint_setSumFin_arcSet_of_nonce {r : ℕ} {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A : Fin r ⊕ Fin r → Finset ℕ} (hA : ∀ j, A j ⊆ S) (hnonce : HasNonce A)
    {α β : Fin r → Circle} (hα : ∀ i, α i ∈ sigmaA (A (Sum.inl i)))
    (hβ : ∀ i, β i ∈ sigmaA (A (Sum.inr i))) {ε : ℝ}
    (hsmall : 2 * (r : ℝ) * ε < 1 / ((∏ j, QA (A j) : ℕ) : ℝ)) :
    Disjoint (setSumFin r (fun i => arcSet (α i) ε))
      (setSumFin r (fun i => arcSet (β i) ε)) := by
  classical
  rw [Set.disjoint_left]
  intro ξ h1 h2'
  rw [mem_setSumFin_arcSet] at h1 h2'
  obtain ⟨θ, hθ, hsum1⟩ := h1
  obtain ⟨θ', hθ', hsum2⟩ := h2'
  have hαmem := hα
  have hβmem := hβ
  choose a ha using hα
  choose b hb using hβ
  obtain ⟨q, j, hqj, huniq⟩ := hnonce
  set sgn : Fin r ⊕ Fin r → ℤ := Sum.elim (fun _ => (1 : ℤ)) (fun _ => (-1 : ℤ)) with hsgn
  have hsgn' : ∀ i, sgn i = 1 ∨ sgn i = -1 := by rintro (i | i) <;> simp [sgn]
  have hAcop : ∀ j : Fin r ⊕ Fin r,
      Nat.Coprime ((Sum.elim a b j)).natAbs (QA (A j)) := by
    rintro (i | i)
    · exact (ha i).1
    · exact (hb i).1
  have hθe : ∀ j : Fin r ⊕ Fin r, |(Sum.elim θ θ' j)| ≤ ε := by
    rintro (i | i)
    · simpa using hθ i
    · simpa using hθ' i
  have h0 := sigmaA_nonce_sum_perturbed_ne_zero h2 hS hA hsgn' (a := Sum.elim a b) hAcop
    ⟨j, q, hqj, fun i hi hqi => hi (huniq i hqi)⟩ (θ := Sum.elim θ θ') (ε := ε) hθe (by
      have hc : (Fintype.card (Fin r ⊕ Fin r) : ℝ) = 2 * (r : ℝ) := by
        rw [Fintype.card_sum, Fintype.card_fin]
        push_cast
        ring
      rw [hc]
      exact hsmall)
  have hterm : ∀ i : Fin r, (1 : ℤ) • (arcPt (QA (A (Sum.inl i))) (a i) + (θ i : Circle))
      + (-1 : ℤ) • (arcPt (QA (A (Sum.inr i))) (b i) + (θ' i : Circle))
      = (α i + (θ i : Circle)) - (β i + (θ' i : Circle)) := by
    intro i
    rw [one_smul, neg_one_smul, ← (ha i).2, ← (hb i).2, sub_eq_add_neg]
  have hsum : (∑ j : Fin r ⊕ Fin r, sgn j • (arcPt (QA (A j)) (Sum.elim a b j)
      + ((Sum.elim θ θ' j : ℝ) : Circle))) = 0 := by
    rw [Fintype.sum_sum_type]
    simp only [sgn, Sum.elim_inl, Sum.elim_inr]
    rw [← Finset.sum_add_distrib]
    simp only [hterm]
    rw [Finset.sum_sub_distrib, hsum1, hsum2, sub_self]
  exact h0 hsum

/-- **Tao's `ortho`(ii) in the frequency-side formulation** (arXiv:2008.05066, §4): if the functions
`F i` have Fourier support in the arcs `α i + [-ε,ε]` of the first half of a nonce family and the
`G i` in the arcs `β i + [-ε,ε]` of the second half, and the `(r,c)`-good smallness holds, then the
pairing `∫ (✻_i F i) · conj (✻_i G i)` of the convolved transforms vanishes. -/
theorem integral_circConvFin_mul_conj_eq_zero_of_nonce {n : ℕ} {S : Finset ℕ}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A : Fin (n + 1) ⊕ Fin (n + 1) → Finset ℕ} (hA : ∀ j, A j ⊆ S) (hnonce : HasNonce A)
    {F G : Fin (n + 1) → Circle → ℂ} {α β : Fin (n + 1) → Circle} {ε : ℝ}
    (hF : ∀ i, ∀ ξ, ξ ∉ arcSet (α i) ε → F i ξ = 0)
    (hG : ∀ i, ∀ ξ, ξ ∉ arcSet (β i) ε → G i ξ = 0)
    (hα : ∀ i, α i ∈ sigmaA (A (Sum.inl i))) (hβ : ∀ i, β i ∈ sigmaA (A (Sum.inr i)))
    (hsmall : 2 * ((n + 1 : ℕ) : ℝ) * ε < 1 / ((∏ j, QA (A j) : ℕ) : ℝ)) :
    ∫ ξ, circConvFin (n + 1) F ξ * star (circConvFin (n + 1) G ξ) ∂AddCircle.haarAddCircle
      = 0 :=
  integral_circConvFin_mul_conj_eq_zero hF hG
    (disjoint_setSumFin_arcSet_of_nonce h2 hS hA hnonce hα hβ hsmall)

/-! ## The discrete Fourier transform of a function on `ℤ` -/

/-- The **discrete Fourier transform** of a function `h : ℤ → ℂ`, as a function on the circle
`𝕋 = ℝ/ℤ`: `𝓕h ξ = Σ'_n h n · e^{2πi n ξ}` (`fourier n ξ = e^{2πi n ξ}` is Mathlib's exponential
monomial `AddCircle.fourier`).  For finitely supported `h` this is a finite sum, which is the only
case used below. -/
noncomputable def discFourier (h : ℤ → ℂ) (ξ : Circle) : ℂ := ∑' n : ℤ, h n * fourier n ξ

/-- For a function vanishing outside a finite set `s`, the discrete Fourier transform is the finite
sum over `s`. -/
lemma discFourier_eq_sum_of_support {h : ℤ → ℂ} {s : Finset ℤ} (hs : ∀ n, n ∉ s → h n = 0)
    (ξ : Circle) : discFourier h ξ = ∑ n ∈ s, h n * fourier n ξ := by
  rw [discFourier, tsum_eq_sum]
  exact fun n hn => by rw [hs n hn, zero_mul]

/-- The discrete Fourier transform of a finitely supported function is a finite sum. -/
lemma discFourier_eq_sum {h : ℤ → ℂ} (hh : (Function.support h).Finite) (ξ : Circle) :
    discFourier h ξ = ∑ n ∈ hh.toFinset, h n * fourier n ξ :=
  discFourier_eq_sum_of_support (fun n hn => by
    by_contra hne
    exact hn (hh.mem_toFinset.mpr hne)) ξ

/-- The discrete Fourier transform of the Kronecker delta at `n` is the character `fourier n`. -/
lemma discFourier_single (n : ℤ) (ξ : Circle) :
    discFourier (fun m => if m = n then (1 : ℂ) else 0) ξ = fourier n ξ := by
  rw [discFourier_eq_sum_of_support (s := {n}) (fun m hm => by
    simp only [Finset.mem_singleton] at hm; simp [hm]) ξ, Finset.sum_singleton]
  simp

/-- `𝓕h 0 = Σ_n h n` for finitely supported `h` (the `0`-th Fourier coefficient is the mass). -/
lemma discFourier_zero_eq_sum {h : ℤ → ℂ} {s : Finset ℤ} (hs : ∀ n, n ∉ s → h n = 0) :
    discFourier h 0 = ∑ n ∈ s, h n := by
  rw [discFourier_eq_sum_of_support hs 0]
  refine Finset.sum_congr rfl fun n _ => ?_
  have h1 : fourier n (0 : Circle) = 1 := by
    rw [show (0 : Circle) = ((0 : ℝ) : Circle) from rfl, fourier_coe_apply]
    simp
  rw [h1, mul_one]

/-! ## The `(r,c)`-good parameterisation -/

/-- **Tao's `ortho`(iii) in the `(r,c)`-good parameterisation**, directly in the form of
arXiv:2008.05066, §4: petals `P i` of cardinality `≤ k'`, `q_max` bounding the elements of `S`, and
the goodness condition `ε < c/(2(n+1) q_max^{2(n+1)k'})` with `0 < c < 1`. -/
theorem disjoint_setSumFin_arcSet_of_petal_of_good {n : ℕ} {S : Finset ℕ}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {P : Fin (n + 1) → Finset ℕ} (hP : ∀ i, P i ⊆ S)
    (hdisj : ∀ i j : Fin (n + 1), i ≠ j → Disjoint (P i) (P j))
    {α β : Fin (n + 1) → Circle} (hα : ∀ i, α i ∈ sigmaA (P i)) (hβ : ∀ i, β i ∈ sigmaA (P i))
    (hne : ∃ i, α i ≠ β i) {ε c : ℝ} {k' qmax : ℕ}
    (hPcard : ∀ i, (P i).card ≤ k') (hmax : ∀ q ∈ S, q ≤ qmax)
    (hc : 0 < c) (hc1 : c < 1)
    (hgood : ε < c / (2 * (n + 1) * (qmax : ℝ) ^ (2 * (n + 1) * k'))) :
    Disjoint (setSumFin (n + 1) (fun i => arcSet (α i) ε))
      (setSumFin (n + 1) (fun i => arcSet (β i) ε)) := by
  refine disjoint_setSumFin_arcSet_of_petal h2 hS hP hdisj hα hβ hne ?_
  -- `q_max ≥ 2`, since some arc is non-degenerate
  have hqmax2 : 2 ≤ qmax := by
    obtain ⟨i₀, hne₀⟩ := hne
    have hpet : P i₀ ≠ ∅ := by
      intro hempty
      have h1 : ∀ x ∈ sigmaA (P i₀), x = 0 := by
        rintro x ⟨a, -, rfl⟩
        rw [hempty]
        show arcPt (QA (∅ : Finset ℕ)) a = 0
        rw [show QA (∅ : Finset ℕ) = 1 from rfl, arcPt_one]
      exact hne₀ (by rw [h1 _ (hα i₀), h1 _ (hβ i₀)])
    obtain ⟨q₀, hq₀⟩ := Finset.nonempty_iff_ne_empty.mpr hpet
    exact le_trans (h2 q₀ (hP i₀ hq₀)) (hmax q₀ (hP i₀ hq₀))
  have hqmax1 : 1 ≤ qmax := by omega
  have hqmax0 : (0 : ℝ) < (qmax : ℝ) := by exact_mod_cast hqmax1
  have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  -- `∏_i Q_{P i} ≤ q_max^{(n+1)k'}`
  have hQle : ∀ i, QA (P i) ≤ qmax ^ k' := by
    intro i
    calc QA (P i) = ∏ q ∈ P i, q := rfl
      _ ≤ ∏ _q ∈ P i, qmax := by
            refine Finset.prod_le_prod₀ (fun q _ => Nat.zero_le q) fun q hq => hmax q (hP i hq)
      _ = qmax ^ (P i).card := by rw [Finset.prod_const]
      _ ≤ qmax ^ k' := Nat.pow_le_pow_right hqmax1 (hPcard i)
  have hProd : (∏ i, QA (P i)) ≤ qmax ^ ((n + 1) * k') := by
    calc (∏ i, QA (P i)) ≤ ∏ _i : Fin (n + 1), qmax ^ k' :=
          Finset.prod_le_prod₀ (fun i _ => Nat.zero_le _) fun i _ => hQle i
      _ = (qmax ^ k') ^ ((n + 1 : ℕ)) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = qmax ^ (k' * (n + 1)) := by rw [← pow_mul]
      _ = qmax ^ ((n + 1) * k') := by congr 1; ring
  have hQpos : (0 : ℝ) < ((∏ i, QA (P i) : ℕ) : ℝ) := by
    have hp : 0 < ∏ i, QA (P i) := Finset.prod_pos fun i _ => by
      have h1 : 1 ≤ QA (P i) := by
        show 1 ≤ ∏ q ∈ P i, q
        exact Finset.one_le_prod₀ fun q hq => by have := h2 q (hP i hq); omega
      omega
    exact_mod_cast hp
  have hcast : (((qmax ^ ((n + 1) * k') : ℕ)) : ℝ) = (qmax : ℝ) ^ ((n + 1) * k') :=
    Nat.cast_pow _ _
  have hQleR : ((∏ i, QA (P i) : ℕ) : ℝ) ≤ (qmax : ℝ) ^ ((n + 1) * k') := by
    rw [← hcast]; exact_mod_cast hProd
  have hqp : (0 : ℝ) < (qmax : ℝ) ^ (2 * (n + 1) * k') := by positivity
  have hqp' : (0 : ℝ) < (qmax : ℝ) ^ ((n + 1) * k') := by positivity
  have hstep1 : 2 * ((n + 1 : ℕ) : ℝ) * ε
      < c / (qmax : ℝ) ^ (2 * (n + 1) * k') := by
    have h := mul_lt_mul_of_pos_left hgood (by linarith : (0 : ℝ) < 2 * ((n + 1 : ℕ) : ℝ))
    rw [show 2 * ((n + 1 : ℕ) : ℝ) * (c / (2 * (n + 1) * (qmax : ℝ) ^ (2 * (n + 1) * k')))
        = c / (qmax : ℝ) ^ (2 * (n + 1) * k') by
      push_cast
      field_simp] at h
    exact h
  have hstep2 : c / (qmax : ℝ) ^ (2 * (n + 1) * k')
      ≤ 1 / (qmax : ℝ) ^ ((n + 1) * k') := by
    rw [div_le_div_iff₀ hqp hqp']
    have h1 : (1 : ℝ) ≤ (qmax : ℝ) ^ ((n + 1) * k') := one_le_pow₀ (by exact_mod_cast hqmax1)
    have h2 : (qmax : ℝ) ^ ((n + 1) * k') ≤ (qmax : ℝ) ^ (2 * (n + 1) * k') := by
      refine pow_le_pow_right₀ (by exact_mod_cast hqmax1) ?_
      rw [show 2 * (n + 1) * k' = 2 * ((n + 1) * k') by ring]
      exact Nat.le_mul_of_pos_left _ (by norm_num)
    nlinarith [h1, h2, hc1.le]
  have hstep3 : 1 / (qmax : ℝ) ^ ((n + 1) * k') ≤ 1 / ((∏ i, QA (P i) : ℕ) : ℝ) :=
    one_div_le_one_div_of_le hQpos hQleR
  calc 2 * ((n + 1 : ℕ) : ℝ) * ε
      < c / (qmax : ℝ) ^ (2 * (n + 1) * k') := hstep1
    _ ≤ 1 / (qmax : ℝ) ^ ((n + 1) * k') := hstep2
    _ ≤ 1 / ((∏ i, QA (P i) : ℕ) : ℝ) := hstep3

/-- **Tao's `ortho`(ii) in the `(r,c)`-good parameterisation** (arXiv:2008.05066, §4), end to end on
the Fourier side: if `F i` has Fourier support in the arc `α i + [-ε,ε]`, `G i` in
`β i + [-ε,ε]`, the family `A : Fin (n+1) ⊕ Fin (n+1) → Finset ℕ` of subsets of the pairwise coprime
`S` carries a nonce and has `|A j| ≤ k`, and the goodness condition
`ε < c/(2(n+1) q_max^{2(n+1)k})` holds, then `∫ (✻_i F i) · conj (✻_i G i) = 0`. -/
theorem integral_circConvFin_mul_conj_eq_zero_of_nonce_of_good {n : ℕ} {S : Finset ℕ}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A : Fin (n + 1) ⊕ Fin (n + 1) → Finset ℕ} (hA : ∀ j, A j ⊆ S) (hnonce : HasNonce A)
    {F G : Fin (n + 1) → Circle → ℂ} {α β : Fin (n + 1) → Circle} {ε c : ℝ} {k qmax : ℕ}
    (hF : ∀ i, ∀ ξ, ξ ∉ arcSet (α i) ε → F i ξ = 0)
    (hG : ∀ i, ∀ ξ, ξ ∉ arcSet (β i) ε → G i ξ = 0)
    (hα : ∀ i, α i ∈ sigmaA (A (Sum.inl i))) (hβ : ∀ i, β i ∈ sigmaA (A (Sum.inr i)))
    (hAcard : ∀ j, (A j).card ≤ k) (hmax : ∀ q ∈ S, q ≤ qmax)
    (hc : 0 < c) (hc1 : c < 1)
    (hgood : ε < c / (2 * (n + 1) * (qmax : ℝ) ^ (2 * (n + 1) * k))) :
    ∫ ξ, circConvFin (n + 1) F ξ * star (circConvFin (n + 1) G ξ) ∂AddCircle.haarAddCircle
      = 0 := by
  refine integral_circConvFin_mul_conj_eq_zero hF hG
    (disjoint_setSumFin_arcSet_of_nonce h2 hS hA hnonce hα hβ ?_)
  -- reduce the smallness to `q_max^{2(n+1)k}` bounding `∏_j Q_{A j}`
  -- `q_max ≥ 2`, since the nonce supplies a nonempty `A j`
  obtain ⟨q₀, j₀, hq₀, -⟩ := hnonce
  have hqmax2 : 2 ≤ qmax := le_trans (h2 q₀ (hA j₀ hq₀)) (hmax q₀ (hA j₀ hq₀))
  have hqmax1 : 1 ≤ qmax := by omega
  have hQle : ∀ j, QA (A j) ≤ qmax ^ k := by
    intro j
    calc QA (A j) = ∏ q ∈ A j, q := rfl
      _ ≤ ∏ _q ∈ A j, qmax := by
            refine Finset.prod_le_prod₀ (fun q _ => Nat.zero_le q) fun q hq => hmax q (hA j hq)
      _ = qmax ^ (A j).card := by rw [Finset.prod_const]
      _ ≤ qmax ^ k := Nat.pow_le_pow_right hqmax1 (hAcard j)
  have hProd : (∏ j, QA (A j)) ≤ qmax ^ (2 * (n + 1) * k) := by
    calc (∏ j, QA (A j)) ≤ ∏ _j : Fin (n + 1) ⊕ Fin (n + 1), qmax ^ k :=
          Finset.prod_le_prod₀ (fun j _ => Nat.zero_le _) fun j _ => hQle j
      _ = (qmax ^ k) ^ (2 * (n + 1)) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin]
            ring_nf
      _ = qmax ^ (k * (2 * (n + 1))) := by rw [← pow_mul]
      _ = qmax ^ (2 * (n + 1) * k) := by congr 1; ring
  have hQpos : (0 : ℝ) < ((∏ j, QA (A j) : ℕ) : ℝ) := by
    have hp : 0 < ∏ j, QA (A j) := Finset.prod_pos fun j _ => by
      have h1 : 1 ≤ QA (A j) := by
        show 1 ≤ ∏ q ∈ A j, q
        exact Finset.one_le_prod₀ fun q hq => by have := h2 q (hA j hq); omega
      omega
    exact_mod_cast hp
  have hcast : (((qmax ^ (2 * (n + 1) * k) : ℕ)) : ℝ) = (qmax : ℝ) ^ (2 * (n + 1) * k) :=
    Nat.cast_pow _ _
  have hQleR : ((∏ j, QA (A j) : ℕ) : ℝ) ≤ (qmax : ℝ) ^ (2 * (n + 1) * k) := by
    rw [← hcast]; exact_mod_cast hProd
  have hqp : (0 : ℝ) < (qmax : ℝ) ^ (2 * (n + 1) * k) := by
    have : (0 : ℝ) < (qmax : ℝ) := by exact_mod_cast hqmax1
    positivity
  have hrr : (0 : ℝ) < 2 * ((n + 1 : ℕ) : ℝ) := by positivity
  have hstep1 : 2 * ((n + 1 : ℕ) : ℝ) * ε < c / (qmax : ℝ) ^ (2 * (n + 1) * k) := by
    have h := mul_lt_mul_of_pos_left hgood hrr
    rw [show 2 * ((n + 1 : ℕ) : ℝ) * (c / (2 * (n + 1) * (qmax : ℝ) ^ (2 * (n + 1) * k)))
        = c / (qmax : ℝ) ^ (2 * (n + 1) * k) by
      push_cast
      field_simp] at h
    exact h
  have hstep2 : c / (qmax : ℝ) ^ (2 * (n + 1) * k)
      ≤ 1 / ((∏ j, QA (A j) : ℕ) : ℝ) := by
    calc c / (qmax : ℝ) ^ (2 * (n + 1) * k)
        ≤ 1 / (qmax : ℝ) ^ (2 * (n + 1) * k) :=
          div_le_div_of_nonneg_right hc1.le hqp.le
      _ ≤ 1 / ((∏ j, QA (A j) : ℕ) : ℝ) := one_div_le_one_div_of_le hQpos hQleR
  exact lt_of_lt_of_le hstep1 hstep2

end Work.BourgainPlan.IonescuWainger
