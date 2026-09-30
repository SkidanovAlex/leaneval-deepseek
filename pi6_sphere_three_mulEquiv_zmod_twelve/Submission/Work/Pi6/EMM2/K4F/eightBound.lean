import Mathlib
import Submission.Work.Pi6.EMM2.K4Kit
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

/-!
# The row-`q = 0` bound in total degree `8` (area EMM2, K4F)

For a multiplicative Serre spectral sequence `S` over `𝔽₂` of a fibration `p : E → B`
through total degree `N ≥ 8` with

* `dim H⁰(F) = 1`, `H¹(F) = H²(F) = 0` (`F = Fib p e₀` the fibre);
* `H¹(B) = H²(B) = H³(B) = 0`, `dim H⁴(B) = 1`, `dim H³(F) = 1`;
* `H⁸(E) = 0`;
* `dim E₈^{0,7} ≤ 1`,

we have `dim H⁸(B) ≤ 2`.

The proof is the row-`0` telescoped dimension bound, **truncated at page `8`** so that its last
uncontrolled source term `E₂^{0,7} ≅ H⁰(B) ⊗ H⁷(F)` never appears: the surviving drops of
dimension in bidegree `(8,0)` come from the sources `(6,1),…,(1,6)`, of which only `(4,3)`
survives (`dim H⁴(B)·dim H³(F) = 1`), together with the differential `d₈ : E₈^{0,7} → E₈^{8,0}`,
whose image has dimension at most `dim E₈^{0,7} ≤ 1`. -/

namespace Work.Pi6.EMM2.K4F

open CategoryTheory CategoryTheory.Limits

/-- **Telescoped row-`0` bound, truncated at page `m`.**

This is `Work.Pi6.CohSS.finrank_row0_le` stopped at page `m` rather than at the page `n+2`, in
which case the last source term of the usual statement is the (uncontrolled) one coming from
bidegree `(0, n-1)` on page `2`; here that step is never performed. -/
theorem row0Telescope {𝕜 : Type} [Field 𝕜] (S : CohSS 𝕜) (N : ℕ)
    (hbox : ∀ a : ℤ × ℤ, 0 ≤ a.1 → 0 ≤ a.2 → a.1 + a.2 ≤ (N : ℤ) →
      FiniteDimensional 𝕜 (S.E 2 a))
    (n m : ℕ) (hnN : n ≤ N) (hm : 2 ≤ m) :
    Module.finrank 𝕜 (S.E 2 ((n : ℤ), 0)) ≤
      Module.finrank 𝕜 (S.E m ((n : ℤ), 0)) +
        ∑ r ∈ Finset.range (m - 2), Module.finrank 𝕜 (S.E 2 (CohSS.sr n (r + 2))) := by
  have hfd := S.finiteDimensional_E N hbox
  have hsrc_le : ∀ k : ℕ, Module.finrank 𝕜 (S.E (k + 2) (CohSS.sr n (k + 2))) ≤
      Module.finrank 𝕜 (S.E 2 (CohSS.sr n (k + 2))) := by
    intro k
    by_cases h1 : 0 ≤ (CohSS.sr n (k + 2)).1
    · by_cases h2 : 0 ≤ (CohSS.sr n (k + 2)).2
      · refine S.finrank_le_two N hbox _ h1 h2 ?_ k
        simp only [CohSS.sr]
        omega
      · exact S.finrank_le_two_of_neg _ (Or.inr (by omega)) k
    · exact S.finrank_le_two_of_neg _ (Or.inl (by omega)) k
  have hsrc_fd : ∀ k : ℕ, FiniteDimensional 𝕜 (S.E (k + 2) (CohSS.sr n (k + 2))) := by
    intro k
    by_cases h1 : 0 ≤ (CohSS.sr n (k + 2)).1
    · by_cases h2 : 0 ≤ (CohSS.sr n (k + 2)).2
      · exact hfd k _ h1 h2 (by
          simp only [CohSS.sr]
          omega)
      · exact S.finiteDimensional_of_neg (Or.inr (by omega))
    · exact S.finiteDimensional_of_neg (Or.inl (by omega))
  have hstep : ∀ k : ℕ, Module.finrank 𝕜 (S.E (k + 2) ((n : ℤ), 0)) ≤
      Module.finrank 𝕜 (S.E (k + 1 + 2) ((n : ℤ), 0)) +
        Module.finrank 𝕜 (S.E 2 (CohSS.sr n (k + 2))) := by
    intro k
    have hout : IsZero (S.E (k + 2) (((n : ℤ), (0 : ℤ)) + vr (k + 2))) := by
      refine S.isZero_quad (k + 2) _ (Or.inr ?_)
      simp only [vr, Prod.snd_add]
      omega
    have hfin1 : FiniteDimensional 𝕜 (S.E (k + 2) ((n : ℤ), 0)) :=
      hfd k _ (by simp) (by simp) (by simp; omega)
    have hfin2' : FiniteDimensional 𝕜 (S.E (k + 2) (((n : ℤ), (0 : ℤ)) - vr (k + 2))) := by
      rw [CohSS.src_row0_eq n (k + 2)]
      exact hsrc_fd k
    have hmain := S.finrank_le_next (r := k + 2) (by omega) (((n : ℤ), (0 : ℤ))) hfin1 hfin2' hout
    rw [CohSS.src_row0_eq] at hmain
    exact hmain.trans (add_le_add le_rfl (hsrc_le k))
  have key : ∀ k : ℕ, k ≤ m - 2 → Module.finrank 𝕜 (S.E 2 ((n : ℤ), 0)) ≤
      Module.finrank 𝕜 (S.E (k + 2) ((n : ℤ), 0)) +
        ∑ r ∈ Finset.range k, Module.finrank 𝕜 (S.E 2 (CohSS.sr n (r + 2))) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
        intro hk
        have hk' : k ≤ m - 2 := by omega
        have hs := hstep k
        have hik := ih hk'
        rw [Finset.sum_range_succ]
        omega
  have hlast := key (m - 2) le_rfl
  rwa [Nat.sub_add_cancel hm] at hlast

/-- The dimension of `E₂^{sr n (r+2)}` as a product of a base and a fibre dimension. -/
theorem finrank_sr_eq {𝕜 : Type} [Field 𝕜] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (S : CohSS 𝕜) (p : C(E, B)) (e₀ : E) (N : ℕ) (hS : IsSerreMSS S p e₀ N)
    (n r : ℕ) (hr : r + 2 ≤ n) (hn : n ≤ N) :
    Module.finrank 𝕜 (S.E 2 (CohSS.sr n (r + 2))) =
      Module.finrank 𝕜 (Coh 𝕜 B (n - (r + 2))) *
        Module.finrank 𝕜 (Coh 𝕜 (Fib p e₀) (r + 1)) := by
  rw [sr_cast n r hr]
  rw [show r + 2 - 1 = r + 1 from by omega]
  exact e2_finrank S p e₀ N hS (n - (r + 2)) (r + 1) (by omega) (by omega)

theorem eightBound {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (e₀ : E) (N : ℕ) (S : Work.Pi6.CohSS (ZMod 2)) (hS : Work.Pi6.IsSerreMSS S p e₀ N)
    (hN : 8 ≤ N)
    (hBfin : ∀ s : ℕ, s ≤ N → FiniteDimensional (ZMod 2) (Work.Pi6.Coh (ZMod 2) B s))
    (hFfin : ∀ q : ℕ, q ≤ N →
      FiniteDimensional (ZMod 2) (Work.Pi6.Coh (ZMod 2) (Work.Pi6.EMM2.Fib p e₀) q))
    (hF0 : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) (Work.Pi6.EMM2.Fib p e₀) 0) = 1)
    (hB4 : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) B 4) = 1)
    (hF3 : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) (Work.Pi6.EMM2.Fib p e₀) 3) = 1)
    (hB1 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) B 1))
    (hB2 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) B 2))
    (hB3 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) B 3))
    (hF1 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) (Work.Pi6.EMM2.Fib p e₀) 1))
    (hF2 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) (Work.Pi6.EMM2.Fib p e₀) 2))
    (hE8 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) E 8))
    (h8 : Module.finrank (ZMod 2) (S.E 8 ((0 : ℤ), (7 : ℤ))) ≤ 1) :
    Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) B 8) ≤ 2 := by
  -- the box hypothesis: `E₂` is finite-dimensional in every bidegree of the box
  have hbox : ∀ a : ℤ × ℤ, 0 ≤ a.1 → 0 ≤ a.2 → a.1 + a.2 ≤ (N : ℤ) →
      FiniteDimensional (ZMod 2) (S.E 2 a) := by
    intro a h1 h2 h3
    obtain ⟨s, hs⟩ : ∃ s : ℕ, a.1 = (s : ℤ) := ⟨a.1.toNat, by omega⟩
    obtain ⟨q, hq⟩ : ∃ q : ℕ, a.2 = (q : ℤ) := ⟨a.2.toNat, by omega⟩
    have hsN : s ≤ N := by omega
    have hqN : q ≤ N := by omega
    obtain ⟨e2, _⟩ := hS
    haveI := hBfin s hsN
    haveI := hFfin q hqN
    have hpair : a = ((s : ℤ), (q : ℤ)) := by ext <;> simp [hs, hq]
    rw [hpair]
    exact Module.Finite.equiv (e2 s q hsN hqN).symm.toLinearEquiv
  -- dimensions of the vanishing groups
  have hF1z : Module.finrank (ZMod 2) (Coh (ZMod 2) (Fib p e₀) 1) = 0 :=
    k4_finrank_eq_zero_of_isZero_cohom hF1
  have hF2z : Module.finrank (ZMod 2) (Coh (ZMod 2) (Fib p e₀) 2) = 0 :=
    k4_finrank_eq_zero_of_isZero_cohom hF2
  have hB1z : Module.finrank (ZMod 2) (Coh (ZMod 2) B 1) = 0 :=
    k4_finrank_eq_zero_of_isZero_cohom hB1
  have hB2z : Module.finrank (ZMod 2) (Coh (ZMod 2) B 2) = 0 :=
    k4_finrank_eq_zero_of_isZero_cohom hB2
  have hB3z : Module.finrank (ZMod 2) (Coh (ZMod 2) B 3) = 0 :=
    k4_finrank_eq_zero_of_isZero_cohom hB3
  -- the telescoped bound truncated at page `8`
  have htel := row0Telescope S N hbox 8 8 hN (by norm_num)
  -- the step at page `8`: the loss in bidegree `(8,0)` is bounded by `dim E₈^{0,7}`
  have hfd := S.finiteDimensional_E N hbox
  have hE8fin : FiniteDimensional (ZMod 2) (S.E 8 ((8 : ℤ), (0 : ℤ))) :=
    hfd 6 _ (by norm_num) (by norm_num) (by omega)
  have h07fin : FiniteDimensional (ZMod 2) (S.E 8 ((0 : ℤ), (7 : ℤ))) :=
    hfd 6 _ (by norm_num) (by norm_num) (by omega)
  have step8 : Module.finrank (ZMod 2) (S.E 8 ((8 : ℤ), (0 : ℤ))) ≤
      Module.finrank (ZMod 2) (S.E 9 ((8 : ℤ), (0 : ℤ))) +
        Module.finrank (ZMod 2) (S.E 8 ((0 : ℤ), (7 : ℤ))) := by
    have hsub : ((8 : ℤ), (0 : ℤ)) - vr 8 = ((0 : ℤ), (7 : ℤ)) := by
      ext <;> simp [vr]
    have hout : IsZero (S.E 8 (((8 : ℤ), (0 : ℤ)) + vr 8)) := by
      refine S.isZero_quad 8 _ (Or.inr ?_)
      simp only [vr, Prod.snd_add]
      norm_num
    have hfin2 : FiniteDimensional (ZMod 2) (S.E 8 (((8 : ℤ), (0 : ℤ)) - vr 8)) := by
      rw [hsub]
      exact h07fin
    have h := S.finrank_le_next (r := 8) (by norm_num) (((8 : ℤ), (0 : ℤ))) hE8fin hfin2 hout
    rw [hsub] at h
    exact h
  -- the step at page `9`: no incoming differential in `(8,0)`
  have step9 : Module.finrank (ZMod 2) (S.E 9 ((8 : ℤ), (0 : ℤ))) ≤
      Module.finrank (ZMod 2) (S.E 10 ((8 : ℤ), (0 : ℤ))) := by
    have hsub : ((8 : ℤ), (0 : ℤ)) - vr 9 = ((-1 : ℤ), (8 : ℤ)) := by
      ext <;> simp [vr]
    have hout : IsZero (S.E 9 (((8 : ℤ), (0 : ℤ)) + vr 9)) := by
      refine S.isZero_quad 9 _ (Or.inr ?_)
      simp only [vr, Prod.snd_add]
      norm_num
    have hfin1 : FiniteDimensional (ZMod 2) (S.E 9 ((8 : ℤ), (0 : ℤ))) :=
      hfd 7 _ (by norm_num) (by norm_num) (by omega)
    have hfin2 : FiniteDimensional (ZMod 2) (S.E 9 (((8 : ℤ), (0 : ℤ)) - vr 9)) := by
      rw [hsub]
      exact S.finiteDimensional_of_neg (Or.inl (by norm_num))
    have h := S.finrank_le_next (r := 9) (by norm_num) (((8 : ℤ), (0 : ℤ))) hfin1 hfin2 hout
    rw [hsub] at h
    have hz : Module.finrank (ZMod 2) (S.E 9 ((-1 : ℤ), (8 : ℤ))) = 0 :=
      S.finrank_eq_zero_of_neg (Or.inl (by norm_num))
    rw [hz, add_zero] at h
    exact h
  -- `E₁₀^{8,0} = E_{8+2}^{8,0}` computes `H⁸(E) = 0`
  have hE10 : Module.finrank (ZMod 2) (S.E 10 ((8 : ℤ), (0 : ℤ))) = 0 := by
    have h1 := finrank_Einfinity_row0_le S p e₀ N hS 8 hN
    have h2 : Module.finrank (ZMod 2) (Coh (ZMod 2) E 8) = 0 :=
      k4_finrank_eq_zero_of_isZero_cohom hE8
    have h3 : Module.finrank (ZMod 2) (S.E (8 + 2) ((8 : ℤ), (0 : ℤ))) = 0 :=
      Nat.le_zero.mp (by linarith)
    simpa using h3
  -- the sum of the six source terms is `1`
  have hsum : (∑ r ∈ Finset.range (8 - 2),
      Module.finrank (ZMod 2) (S.E 2 (CohSS.sr 8 (r + 2)))) = 1 := by
    rw [Finset.sum_eq_single (2 : ℕ)]
    · rw [finrank_sr_eq S p e₀ N hS 8 2 (by norm_num) hN]
      rw [show (8 : ℕ) - (2 + 2) = 4 from by norm_num,
        show (2 + 1 : ℕ) = 3 from by norm_num]
      rw [hB4, hF3, one_mul]
    · intro b hb hb2
      rw [Finset.mem_range] at hb
      have hb6 : b < 6 := by omega
      rw [finrank_sr_eq S p e₀ N hS 8 b (by omega) hN]
      interval_cases b
      · rw [show (8 : ℕ) - (0 + 2) = 6 from by norm_num,
          show (0 + 1 : ℕ) = 1 from by norm_num, hF1z, mul_zero]
      · rw [show (8 : ℕ) - (1 + 2) = 5 from by norm_num,
          show (1 + 1 : ℕ) = 2 from by norm_num, hF2z, mul_zero]
      · exact absurd rfl hb2
      · rw [show (8 : ℕ) - (3 + 2) = 3 from by norm_num,
          show (3 + 1 : ℕ) = 4 from by norm_num, hB3z, zero_mul]
      · rw [show (8 : ℕ) - (4 + 2) = 2 from by norm_num,
          show (4 + 1 : ℕ) = 5 from by norm_num, hB2z, zero_mul]
      · rw [show (8 : ℕ) - (5 + 2) = 1 from by norm_num,
          show (5 + 1 : ℕ) = 6 from by norm_num, hB1z, zero_mul]
    · intro h
      exact absurd (Finset.mem_range.mpr (by norm_num : 2 < 8 - 2)) h
  -- `dim H⁸(B) = dim E₂^{8,0}`
  have he2 : Module.finrank (ZMod 2) (S.E 2 ((8 : ℤ), (0 : ℤ))) =
      Module.finrank (ZMod 2) (Coh (ZMod 2) B 8) := by
    have h := e2_finrank S p e₀ N hS 8 0 hN (by omega)
    rw [hF0, mul_one] at h
    exact h
  rw [← he2]
  linarith [htel, step8, step9, hE10, hsum, h8]

end Work.Pi6.EMM2.K4F
