import Mathlib
import Submission.Work.BMF.adi_all_defs
import Submission.Work.BMF.primesIn_card_le_pi0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Polynomial Finset Real Complex

/-- Membership in `primesIn` from the unfolding predicate `IsPrimeIn`. -/
lemma mem_primesIn_of_isPrimeIn {a b : ℝ} {p : ℕ} (h : IsPrimeIn a b p) :
    p ∈ primesIn a b := by
  rw [primesIn, natIcc, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨Nat.ceil_le.mpr h.2.1, Nat.le_floor h.2.2⟩, h.1⟩

/-- The number of edges of a `QuadData` is bounded by `≍ π₀(P₁)² · #fam`.

Each edge `e ∈ D.edges` is recorded by the triple `(e.p₁, e.p₂, e.x₂)` with `p₁, p₂` primes in
`[P₁, 2P₁]` and `x₂ ∈ fam`.  This map is *injective*: if two edges share `p₁, p₂, x₂` then
`EdgeGeom` puts both left endpoints `x₁` inside the same window of length `200 L`, while `IsFam`
`500 L`-separates the elements of `fam`; since `L > 0`, the two endpoints coincide.  Hence
`#edges ≤ (#primes in [P₁, 2P₁])² · #fam`, and `#primes in [P₁, 2P₁] ≤ C π₀(P₁)` by Chebyshev. -/
theorem edges_card_le {k : ℕ} {f : ℕ → ℂ} :
    ∃ C P₀ : ℝ, 0 < C ∧ ∀ (c Cq X L P₁ P₂ : ℝ) (D : Work.BMF.QuadData k f c Cq X L P₁ P₂),
      P₀ ≤ P₁ → 0 < P₁ → 0 < L → 8000 * P₁ ^ 2 < X / L →
      (D.edges.card : ℝ) ≤ C * Work.BMF.pi0 P₁ ^ 2 * ((D.fam.card : ℝ) + 1) := by
  classical
  obtain ⟨C', P₀', hC', hprimes⟩ := primesIn_card_le_pi0
  refine ⟨C' ^ 2, max P₀' 2, by positivity, ?_⟩
  intro c Cq X L P₁ P₂ D hP₀ hP₁ hL hX
  have hleP₀' : P₀' ≤ P₁ := le_trans (le_max_left _ _) hP₀
  have hge2 : (2 : ℝ) ≤ P₁ := le_trans (le_max_right _ _) hP₀
  have hP₁1 : (1 : ℝ) < P₁ := by linarith
  have hP₁pos : 0 < P₁ := by linarith
  have hpi0nn : 0 ≤ pi0 P₁ := div_nonneg (le_of_lt hP₁pos) (le_of_lt (Real.log_pos hP₁1))
  set n : ℕ := (primesIn P₁ (2 * P₁)).card with hn
  have hnR : (n : ℝ) ≤ C' * pi0 P₁ := by
    simpa only [hn] using hprimes P₁ hleP₀'
  -- the injection `e ↦ (e.p₁, e.p₂, e.x₂)`
  have hinj : Set.InjOn (fun e : Edge => (e.p₁, e.p₂, e.x₂)) ↑D.edges := by
    intro e he e' he' h
    have hp₁ : e.p₁ = e'.p₁ := by simpa using congrArg (fun t : ℕ × ℕ × ℝ => t.1) h
    have hp₂ : e.p₂ = e'.p₂ := by simpa using congrArg (fun t : ℕ × ℕ × ℝ => t.2.1) h
    have hx₂ : e.x₂ = e'.x₂ := by simpa using congrArg (fun t : ℕ × ℕ × ℝ => t.2.2) h
    have hge := D.geom e he
    have hge' := D.geom e' he'
    unfold EdgeGeom at hge hge'
    obtain ⟨hx₁S, _, _, _, _, _, habs⟩ := hge
    obtain ⟨hx₁S', _, _, _, _, _, habs'⟩ := hge'
    -- both `x₁`'s lie within `100 L` of the same point `c`
    have h1 : |e.x₁ - ((e'.p₂ : ℝ) / e'.p₁) * e'.x₂| ≤ 100 * L := by
      rw [← hp₁, ← hp₂, ← hx₂]; exact habs
    have h2 : |e'.x₁ - ((e'.p₂ : ℝ) / e'.p₁) * e'.x₂| ≤ 100 * L := habs'
    have htri := abs_sub_le e.x₁ (((e'.p₂ : ℝ) / e'.p₁) * e'.x₂) e'.x₁
    have h3 : |(((e'.p₂ : ℝ) / e'.p₁) * e'.x₂) - e'.x₁| ≤ 100 * L := by
      rw [abs_sub_comm]; exact h2
    have hsep : |e.x₁ - e'.x₁| ≤ 200 * L := by linarith
    by_cases hx₁ : e.x₁ = e'.x₁
    · cases e; cases e'; simp_all
    · exfalso
      have hsep' := D.isFam.2 e.x₁ hx₁S e'.x₁ hx₁S' hx₁
      have : (200 : ℝ) * L < 500 * L := by linarith
      linarith [abs_nonneg (e.x₁ - e'.x₁)]
  -- the image is contained in a product of the two prime sets and `fam`
  have hsub : D.edges.image (fun e : Edge => (e.p₁, e.p₂, e.x₂)) ⊆
      (primesIn P₁ (2 * P₁)) ×ˢ ((primesIn P₁ (2 * P₁)) ×ˢ D.fam) := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨e, he, rfl⟩ := hq
    have hge := D.geom e he
    unfold EdgeGeom at hge
    obtain ⟨_, hx₂S, _, _, hpr1, hpr2, _⟩ := hge
    exact Finset.mem_product.mpr ⟨mem_primesIn_of_isPrimeIn hpr1,
      Finset.mem_product.mpr ⟨mem_primesIn_of_isPrimeIn hpr2, hx₂S⟩⟩
  have hcard2 : (D.edges.image (fun e : Edge => (e.p₁, e.p₂, e.x₂))).card ≤
      n * n * D.fam.card := by
    calc (D.edges.image (fun e : Edge => (e.p₁, e.p₂, e.x₂))).card
        ≤ ((primesIn P₁ (2 * P₁)) ×ˢ ((primesIn P₁ (2 * P₁)) ×ˢ D.fam)).card :=
          Finset.card_le_card hsub
      _ = (primesIn P₁ (2 * P₁)).card * ((primesIn P₁ (2 * P₁)).card * D.fam.card) := by
          rw [Finset.card_product, Finset.card_product]
      _ = n * n * D.fam.card := by rw [hn, mul_assoc]
  have hcardR : (D.edges.card : ℝ) ≤ (n : ℝ) * (n : ℝ) * (D.fam.card : ℝ) := by
    have hcard1 : (D.edges.image (fun e : Edge => (e.p₁, e.p₂, e.x₂))).card = D.edges.card :=
      Finset.card_image_of_injOn hinj
    have h : D.edges.card ≤ n * n * D.fam.card := by rw [← hcard1]; exact hcard2
    calc (D.edges.card : ℝ) ≤ ((n * n * D.fam.card : ℕ) : ℝ) := by exact_mod_cast h
      _ = (n : ℝ) * (n : ℝ) * (D.fam.card : ℝ) := by push_cast; ring
  have hstep : (n : ℝ) * (n : ℝ) * (D.fam.card : ℝ) ≤
      (C' * pi0 P₁) * (C' * pi0 P₁) * (D.fam.card : ℝ) := by
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    have hCp : 0 ≤ C' * pi0 P₁ := mul_nonneg (le_of_lt hC') hpi0nn
    have h1 : (n : ℝ) * (n : ℝ) ≤ (C' * pi0 P₁) * (C' * pi0 P₁) :=
      mul_le_mul hnR hnR hn0 hCp
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  calc (D.edges.card : ℝ)
      ≤ (n : ℝ) * (n : ℝ) * (D.fam.card : ℝ) := hcardR
    _ ≤ (C' * pi0 P₁) * (C' * pi0 P₁) * (D.fam.card : ℝ) := hstep
    _ = C' ^ 2 * pi0 P₁ ^ 2 * (D.fam.card : ℝ) := by ring
    _ ≤ C' ^ 2 * pi0 P₁ ^ 2 * ((D.fam.card : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end Work.BMF
