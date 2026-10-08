/-
# From the pinned form of the squaring form to the model `B`/`C`/`D`

The case analysis of Higman's Lemma 12 (Higman, *Suzuki 2-groups*, Illinois J. Math. **7** (1963),
Lemma 12) — the last missing step of `Work.Higman.squaring_form_classification`.  See
`Submission/Work/Higman/NOTES_cocycle_normal_form.md` §7 for the full plan.

Input: the pinned squaring form of `Q3.L12.pinned_form_axis_type` (`φ`, `ψ`, `ν`, `ν'`, `λ`,
`a`, `a'`, `C`, `C'`, `e`, the axis and cross resonances, and the pinned shape).

Output: `θ`, `ε`, additive automorphisms `Φ`, `Ψ` with `Ψ (Q (Φ v))` equal to the squaring form of
`bCocycle 𝔽 θ ε`, `cCocycle 𝔽 θ ε` or `dCocycle 𝔽 θ ε`.

The four cases are the proved reductions `reduce_ab_ab`, `reduce_r_r`, `reduce_ab_r`, `reduce_r_s`;
getting the pinned data into their hypotheses is the Frobenius normalisation plus the congruence
bookkeeping (`Q3.L12.c_case_congruence`, `Q3.L12.d_case_congruence`, `Q3.L12.two_pow_congruence`,
`Q3.two_pow_add_eq_pow`).
-/
import Mathlib
import Submission.Work.Higman.Q3.Defs
import Submission.Work.Higman.Family
import Submission.Work.Higman.family_anisotropic
import Submission.Work.Higman.Q3.axis_resonance
import Submission.Work.Higman.Q3.two_pow_add_eq_pow
import Submission.Work.Higman.Q3.two_pow_add_eq_two_pow_add
import Submission.Work.Higman.Q3.reduce_ab_ab
import Submission.Work.Higman.Q3.reduce_ab_r
import Submission.Work.Higman.Q3.reduce_r_s
import Submission.Work.Higman.Q3.reduce_r_r
import Submission.Work.Higman.Q3.L12.c_case_congruence
import Submission.Work.Higman.Q3.L12.d_case_congruence
import Submission.Work.Higman.Q3.L12.two_pow_congruence
import Submission.Work.Higman.Q3.L12.pinned_form_axis_type
import Submission.Work.Higman.gcd_two_pow
import Submission.Work.Higman.orderOf_frobeniusEquiv_pow
import Submission.Work.Higman.cocycle_setup
import Submission.Work.Higman.Q3.L12.regular_aut_exists_local
import Submission.Work.Higman.Q3.L12.exists_xi_decomposition
import Submission.Work.Higman.Q3.L12.pinned_canonical
import Submission.Work.Higman.Q3.L12.canonical_dispatch

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Higman.Q3

/-- `bCocycle 𝔽 θ ε` at `(v, v)` in coordinates, when `θ x = x ^ (2 ^ r)`. -/
lemma bCocycle_self_of_pow_l12 {n r : ℕ} {θ : GaloisField 2 n ≃+* GaloisField 2 n}
    (hθ : ∀ x : GaloisField 2 n, θ x = x ^ (2 ^ r)) (ε : GaloisField 2 n)
    (v : GaloisField 2 n × GaloisField 2 n) :
    bCocycle (GaloisField 2 n) θ ε v v =
      v.1 ^ (1 + 2 ^ r) + ε * (v.1 * v.2 ^ (2 ^ r)) + v.2 ^ (1 + 2 ^ r) := by
  have h1 : v.1 ^ (1 + 2 ^ r) = v.1 * v.1 ^ (2 ^ r) := by rw [pow_add, pow_one]
  have h2 : v.2 ^ (1 + 2 ^ r) = v.2 * v.2 ^ (2 ^ r) := by rw [pow_add, pow_one]
  rw [h1, h2]
  simp only [bCocycle, hθ]

/-- **The case analysis of Higman's Lemma 12 (the pinned form ⟹ one of the models).**

`Q v := ψ (b (φ.symm v) (φ.symm v))` has the pinned shape; the inputs are the axis resonances
`∃ i j < n, ν ^ (2 ^ i + 2 ^ j) = λ` (primed for `ν'`) and the cross resonance
`e k l ≠ 0 ⟹ ν ^ (2 ^ k) ν' ^ (2 ^ l) = λ`, and `hanis` is the anisotropy of the pinned form.

The conclusion is the disjunction of `bCocycle`/`cCocycle`/`dCocycle` squaring forms, with the
Column-III conditions on `ε` and `Odd (orderOf θ)`. -/
theorem pinned_to_model_l12
    {n : ℕ} (hn : 2 ≤ n)
    {V W : Type*} [AddCommGroup V] [AddExpTwo V] [AddCommGroup W] [AddExpTwo W]
    {b : V → V → W} [Biadd b]
    (φ : V ≃+ (GaloisField 2 n × GaloisField 2 n)) (ψ : W ≃+ GaloisField 2 n)
    {ν ν' lam : (GaloisField 2 n)ˣ}
    (hν : orderOf ν = 2 ^ n - 1) (hν' : orderOf ν' = 2 ^ n - 1) (hlam : orderOf lam = 2 ^ n - 1)
    {a a' : ℕ} (ha1 : 1 ≤ a) (haq : a ≤ 2 ^ n - 1) (ha'1 : 1 ≤ a') (ha'q : a' ≤ 2 ^ n - 1)
    (haν : (ν : GaloisField 2 n) ^ a = (lam : GaloisField 2 n))
    (ha'ν' : (ν' : GaloisField 2 n) ^ a' = (lam : GaloisField 2 n))
    (hax : ∃ i j : ℕ, i < n ∧ j < n ∧
      (ν : GaloisField 2 n) ^ (2 ^ i + 2 ^ j) = (lam : GaloisField 2 n))
    (hax' : ∃ i j : ℕ, i < n ∧ j < n ∧
      (ν' : GaloisField 2 n) ^ (2 ^ i + 2 ^ j) = (lam : GaloisField 2 n))
    {C C' : GaloisField 2 n} (hC : C ≠ 0) (hC' : C' ≠ 0) {e : ℕ → ℕ → GaloisField 2 n}
    (hres : ∀ k l : ℕ, e k l ≠ 0 →
      (ν : GaloisField 2 n) ^ (2 ^ k) * (ν' : GaloisField 2 n) ^ (2 ^ l) =
        (lam : GaloisField 2 n))
    (hform : ∀ α β : GaloisField 2 n,
      ψ (b (φ.symm (α, β)) (φ.symm (α, β))) = C * α ^ a + C' * β ^ a' +
        ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
          e k l * α ^ (2 ^ k) * β ^ (2 ^ l))
    (hanis : ∀ α β : GaloisField 2 n, (α, β) ≠ 0 →
      C * α ^ a + C' * β ^ a' +
        ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
          e k l * α ^ (2 ^ k) * β ^ (2 ^ l) ≠ 0) :
    ∃ (θ : GaloisField 2 n ≃+* GaloisField 2 n) (ε : GaloisField 2 n)
      (Φ : (GaloisField 2 n × GaloisField 2 n) ≃+ (GaloisField 2 n × GaloisField 2 n))
      (Ψ : GaloisField 2 n ≃+ GaloisField 2 n),
      Odd (orderOf θ) ∧
      ((ε ≠ 0 ∧ (∀ ρ : GaloisField 2 n, ε ≠ ρ⁻¹ + θ ρ) ∧
          ∀ v : GaloisField 2 n × GaloisField 2 n,
            Ψ (ψ (b (φ.symm (Φ v)) (φ.symm (Φ v)))) =
              bCocycle (GaloisField 2 n) θ ε v v)
        ∨ ((∀ x : GaloisField 2 n, (θ (θ x)) ^ 2 = x) ∧
            (∀ ρ : GaloisField 2 n, ε ≠ ρ⁻¹ + θ ρ ^ 2 * ρ) ∧
            ∀ v : GaloisField 2 n × GaloisField 2 n,
              Ψ (ψ (b (φ.symm (Φ v)) (φ.symm (Φ v)))) =
                cCocycle (GaloisField 2 n) θ ε v v)
        ∨ (θ ^ 5 = 1 ∧ θ ≠ RingEquiv.refl _ ∧ 5 ∣ n ∧
            (∀ ρ : GaloisField 2 n, ε ≠ ρ⁻¹ + θ (θ (θ (θ ρ))) * θ ρ * ρ⁻¹) ∧
            ∀ v : GaloisField 2 n × GaloisField 2 n,
              Ψ (ψ (b (φ.symm (Φ v)) (φ.symm (Φ v)))) =
                dCocycle (GaloisField 2 n) θ ε v v)) := by
  have haxp : ∃ i j : ℕ, i < n ∧ j < n ∧
      (ν : GaloisField 2 n) ^ (2 ^ i) * (ν : GaloisField 2 n) ^ (2 ^ j) =
        (lam : GaloisField 2 n) := by
    obtain ⟨i, j, hi, hj, h⟩ := hax
    exact ⟨i, j, hi, hj, by rw [pow_add] at h; exact h⟩
  have hax'p : ∃ i j : ℕ, i < n ∧ j < n ∧
      (ν' : GaloisField 2 n) ^ (2 ^ i) * (ν' : GaloisField 2 n) ^ (2 ^ j) =
        (lam : GaloisField 2 n) := by
    obtain ⟨i, j, hi, hj, h⟩ := hax'
    exact ⟨i, j, hi, hj, by rw [pow_add] at h; exact h⟩
  obtain ⟨r, s, Φe, g, hrn, hsn, hshape, hres', _hsupp, hcopr, hcops, hcase⟩ :=
    Work.Higman.Q3.L12.pinned_canonical hn φ ψ hν hν' hlam ha1 haq ha'1 ha'q haν ha'ν' haxp hax'p
      hC hC' hres hform hanis
  set Q : GaloisField 2 n × GaloisField 2 n → GaloisField 2 n :=
    fun v => ψ (b (φ.symm (Φe v)) (φ.symm (Φe v))) with hQdef
  have hani : ∀ v : GaloisField 2 n × GaloisField 2 n, v ≠ 0 → Q v ≠ 0 := by
    intro v hv
    have hne : Φe v ≠ 0 := fun h0 => hv (Φe.injective (by rw [h0, map_zero]))
    have h := hanis (Φe v).1 (Φe v).2 (by simpa using hne)
    rw [← hform] at h
    simpa [hQdef] using h
  obtain ⟨θ, ε, Φ, Ψ, hodd, hcases⟩ :=
    Work.Higman.Q3.L12.canonical_dispatch hn hrn hsn hC hC' Q hshape hani hres' hcopr hcops hcase
  refine ⟨θ, ε, Φ.trans Φe, Ψ, hodd, ?_⟩
  rcases hcases with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4, h5⟩
  · exact Or.inl ⟨h1, h2, fun v => by
      simpa only [hQdef, AddEquiv.trans_apply] using h3 v⟩
  · exact Or.inr (Or.inl ⟨h1, h2, fun v => by
      simpa only [hQdef, AddEquiv.trans_apply] using h3 v⟩)
  · exact Or.inr (Or.inr ⟨h1, h2, h3, h4, fun v => by
      simpa only [hQdef, AddEquiv.trans_apply] using h5 v⟩)

/-! ## The full chain: the target's hypotheses ⟹ the classification of the squaring form -/

/-- **`squaring_form_classification`, assembled from the chain**

    target hypotheses
      → `Q3.regular_aut_exists`            (a regular `ζ` of order `|W| - 1`)
      → `Q3.L12.exists_xi_decomposition`   (`V = U ⊕ U'`, both of order `|W|`)
      → `Q3.L12.pinned_form_axis_type`     (the pinned shape + the axis resonances)
      → `Q3.pinned_to_model_l12`               (the case analysis)

The statement is exactly that of `Work.Higman.squaring_form_classification`. -/
theorem squaring_form_classification_l12
    {V W : Type} [AddCommGroup V] [AddExpTwo V] [AddCommGroup W] [AddExpTwo W]
    {b : V → V → W} [Biadd b]
    (hcardV : Nat.card V = Nat.card W ^ 2)
    (hW : 4 ≤ Nat.card W)
    (hinvol : ∀ x : TwoStep V W b, x ^ 2 = 1 → x ∈ Subgroup.center (TwoStep V W b))
    (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b))
    (htrans : ∀ x y : TwoStep V W b, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (ξ ^ k) x = y) :
    ∃ (n : ℕ) (φ : V ≃+ (GaloisField 2 n × GaloisField 2 n)) (ψ : W ≃+ GaloisField 2 n)
      (θ : GaloisField 2 n ≃+* GaloisField 2 n) (ε : GaloisField 2 n),
      Nat.card W = 2 ^ n ∧ Odd (orderOf θ) ∧
      ((ε ≠ 0 ∧ (∀ ρ : GaloisField 2 n, ε ≠ ρ⁻¹ + θ ρ) ∧
          ∀ u : V, ψ (b u u) = bCocycle (GaloisField 2 n) θ ε (φ u) (φ u))
        ∨ ((∀ a : GaloisField 2 n, (θ (θ a)) ^ 2 = a) ∧
            (∀ ρ : GaloisField 2 n, ε ≠ ρ⁻¹ + θ ρ ^ 2 * ρ) ∧
            ∀ u : V, ψ (b u u) = cCocycle (GaloisField 2 n) θ ε (φ u) (φ u))
        ∨ (θ ^ 5 = 1 ∧ θ ≠ RingEquiv.refl _ ∧ 5 ∣ n ∧
            (∀ ρ : GaloisField 2 n, ε ≠ ρ⁻¹ + θ (θ (θ (θ ρ))) * θ ρ * ρ⁻¹) ∧
            ∀ u : V, ψ (b u u) = dCocycle (GaloisField 2 n) θ ε (φ u) (φ u))) := by
  haveI : Finite W := Work.Higman.finite_of_hW hW
  haveI : Finite V := Work.Higman.finite_V_of_hcardV hcardV hW
  -- 1. a regular automorphism of order `|W| - 1`
  obtain ⟨ζ, hζord, hζtrans, _⟩ := Work.Higman.Q3.regular_aut_exists hcardV hW hinvol hcenter ξ htrans
  -- 2. the `ζ`-invariant decomposition `V = U ⊕ U'`
  obtain ⟨U, U', hUinv, hU'inv, hsum, hdisj, hUcard, hU'card, hUtrans, hU'trans⟩ :=
    Work.Higman.Q3.L12.exists_xi_decomposition hcardV hW hinvol hcenter ζ hζord hζtrans
  -- 3. the pinned form
  obtain ⟨n, φ₀, ψ₀, ν, ν', lam, a, a', C, C', e, hcard, hn1, hν, hν', hlam, hC, hC', ha1, haq,
    ha'1, ha'q, haν, ha'ν', hax, hax', hfax, hfbx, hres, hform⟩ :=
    Work.Higman.Q3.L12.pinned_form_axis_type hcardV hW hinvol hcenter ζ hζord hζtrans U U'
      hUinv hU'inv hsum hdisj hUcard hU'card hUtrans hU'trans
  -- 4. the anisotropy of the pinned form
  have hanis : ∀ α β : GaloisField 2 n, (α, β) ≠ 0 →
      C * α ^ a + C' * β ^ a' +
        ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
          e k l * α ^ (2 ^ k) * β ^ (2 ^ l) ≠ 0 := by
    intro α β hv hzero
    have hbu : b (φ₀.symm (α, β)) (φ₀.symm (α, β)) = 0 := by
      have h1 := hform α β
      rw [hzero] at h1
      exact ψ₀.injective (by rw [h1, map_zero])
    have h2 : φ₀.symm (α, β) = 0 := (Work.Higman.b_self_eq_zero_iff hinvol hcenter _).mp hbu
    exact hv (by rw [← AddEquiv.apply_symm_apply φ₀ (α, β), h2, map_zero])
  -- 5. the case analysis
  obtain ⟨haxi, haxj, haxin, haxjn, haxeq⟩ := hax
  obtain ⟨haxi', haxj', haxin', haxjn', haxeq'⟩ := hax'
  have hax' : ∃ i j : ℕ, i < n ∧ j < n ∧
      (ν : GaloisField 2 n) ^ (2 ^ i + 2 ^ j) = (lam : GaloisField 2 n) :=
    ⟨haxi, haxj, haxin, haxjn, by rw [pow_add]; exact haxeq⟩
  have hax'' : ∃ i j : ℕ, i < n ∧ j < n ∧
      (ν' : GaloisField 2 n) ^ (2 ^ i + 2 ^ j) = (lam : GaloisField 2 n) :=
    ⟨haxi', haxj', haxin', haxjn', by rw [pow_add]; exact haxeq'⟩
  have hn2 : 2 ≤ n := by
    have h4 : 2 ^ 2 ≤ 2 ^ n := by rw [← hcard]; norm_num; exact hW
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4
  obtain ⟨θ, ε, Φ, Ψ, hθodd, hcases⟩ :=
    pinned_to_model_l12 hn2 φ₀ ψ₀ hν hν' hlam ha1 haq ha'1 ha'q haν ha'ν' hax' hax'' hC hC'
      hres hform hanis
  -- 6. read off the answer in the target's coordinates
  refine ⟨n, φ₀.trans Φ.symm, ψ₀.trans Ψ, θ, ε, hcard, hθodd, ?_⟩
  rcases hcases with ⟨hε, hρ, hv⟩ | ⟨hθ2, hρ, hv⟩ | ⟨h5, h1, h5dvd, hρ, hv⟩
  · exact Or.inl ⟨hε, hρ, fun u => by simpa using hv (Φ.symm (φ₀ u))⟩
  · exact Or.inr (Or.inl ⟨hθ2, hρ, fun u => by simpa using hv (Φ.symm (φ₀ u))⟩)
  · exact Or.inr (Or.inr ⟨h5, h1, h5dvd, hρ, fun u => by
      simpa using hv (Φ.symm (φ₀ u))⟩)

end Work.Higman.Q3
