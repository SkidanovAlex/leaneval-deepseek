import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.Main
import Submission.Work.Hering.AppVII.sum_pair_sq_eq
import Submission.Work.Hering.AppVII.arith_final

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Appendix VII, Part 2: the final counting step

Peterfalvi, Appendix VII, p. 219–220, the last step of Part 2, abstracted from the situation
`H = Q ⋊ P` with `Q` extraspecial and `P` of prime order `p`.

Let `G` be a finite group, `P ≤ G` of prime order `p` (so `P` is cyclic, hence commutative),
and let `χ ∈ Irr G` be an irreducible character whose degree is a power of the odd prime `q`,
`χ(1) = q ^ k ≠ 1`.  Suppose the counting identity

`∑_{s ∈ P} |χ s|² = χ(1)² + (p - 1)`

of step 5 holds.  Then the sum of `χ` over `P` is nonzero — equivalently, the trivial character
of `P` is a constituent of the restriction `Res_P χ` (Peterfalvi: `1_P ⊆ Res_P χ`).

## Proof

Write `f = Res_P χ`, a character of the abelian group `P` of order `p` (as a pullback of a
character of `G` along the inclusion).  Expand `f = ∑_ψ (c ψ) • ψ` over `Irr P` with
`c ψ : ℕ` (`isChar_iff_exists_nat_coeffs`).  Since `P` is commutative every `ψ ∈ Irr P` has
degree one (`irrDeg_eq_one_of_commutative`), hence

* `∑_ψ c ψ = f 1 = χ 1 = q ^ k`,
* `cfInner f f = ∑_ψ (c ψ)²` (orthonormality) and `cfInner f f = p⁻¹ ∑_{s ∈ P} |f s|²`, so the
  counting hypothesis gives `p · ∑_ψ (c ψ)² = χ(1)² + (p - 1)`,
* `⟨f, 1_P⟩ = c (1_P)` and `⟨f, 1_P⟩ = p⁻¹ ∑_{s ∈ P} f s`, so `∑_{s ∈ P} χ s = p · c (1_P)`.

Combining the first two displayed identities with the elementary variance identity
`∑_{ψ,ψ'} (n ψ - n ψ')² = 2 (|Irr P| ∑ n² - (∑ n)²)` (`sum_pair_sq_eq`) and `|Irr P| = p`
(`sum_irr_degree_sq`), the coefficients `n ψ = c ψ` satisfy the hypotheses of the arithmetic
lemma `arith_final`: they are nonnegative integers with `∑_ψ n ψ = q ^ k` and pairwise
differences summing to `2 (p - 1)`.  Hence every `c ψ ≠ 0`; in particular `c (1_P) ≠ 0` and
therefore `∑_{s ∈ P} χ s = p · c (1_P) ≠ 0`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Classical Finset

namespace Work.Hering.AppVII

theorem part2_final_step {G : Type*} [Group G] [Fintype G] {P : Subgroup G} [Fintype ↥P] {p q : ℕ}
    (hp : p.Prime) (hPcard : Nat.card ↥P = p) (hcomm : IsMulCommutative ↥P)
    (hq : q.Prime) (hqodd : Odd q) {χ : G → ℂ} (hχ : χ ∈ Work.CharCore.Irr G)
    (hcount : ∑ s : ↥P, Complex.normSq (χ (s : G)) = (Work.CharCore.irrDeg χ : ℝ) ^ 2 + (p - 1))
    (hpow : ∃ k : ℕ, Work.CharCore.irrDeg χ = q ^ k) (hne1 : Work.CharCore.irrDeg χ ≠ 1) :
    ∑ s : ↥P, χ (s : G) ≠ 0 := by
  classical
  haveI : IsMulCommutative ↥P := hcomm
  let f : ↥P → ℂ := fun s => χ (s : G)
  -- `f` is the character of the representation of `P` obtained by restricting the simple
  -- module affording `χ`.
  have hf : Work.CharCore.IsChar f := by
    obtain ⟨N, hN, hNχ⟩ := Work.CharCore.exists_mem_irrSubmodules_of_mem_Irr hχ
    have hchar : Representation.character ((Work.CharCore.submoduleRep N).comp P.subtype) = f := by
      funext s
      show (Work.CharCore.submoduleRep N).character (s : G) = f s
      rw [hNχ]
    rw [← hchar]
    exact Work.CharCore.isChar_character _
  -- the multiplicities of the irreducible constituents of `f`
  obtain ⟨c, hc⟩ := (Work.CharCore.isChar_iff_exists_nat_coeffs (G := ↥P)).mp hf
  -- all irreducible characters of `P` have degree one
  have hdeg : ∀ (ψ : ↥P → ℂ), ψ ∈ Work.CharCore.Irr ↥P → ψ 1 = 1 := by
    intro ψ hψ
    rw [Work.CharCore.irrDeg_spec hψ, Work.CharCore.irrDeg_eq_one_of_commutative hψ]
    norm_num
  -- `P` has `p` irreducible characters
  have hcard_irr : Fintype.card ↥(Work.CharCore.Irr ↥P) = p := by
    have hsum0 := Work.CharCore.sum_irr_degree_sq (G := ↥P)
    have hterm : ∀ ψ ∈ Work.CharCore.Irr ↥P, (ψ : ↥P → ℂ) 1 ^ 2 = (1 : ℂ) := fun ψ hψ => by
      rw [hdeg ψ hψ]; norm_num
    have hcongr : (∑ ψ ∈ Work.CharCore.Irr ↥P, (ψ : ↥P → ℂ) 1 ^ 2)
        = ((Work.CharCore.Irr ↥P).card : ℂ) := by
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
    have h2 : (((Work.CharCore.Irr ↥P).card : ℕ) : ℂ) = (p : ℂ) := by
      rw [← hcongr, hsum0, hPcard]
    exact (Fintype.card_coe _).trans (Nat.cast_injective h2)
  obtain ⟨k, hk⟩ := hpow
  -- the sum of the multiplicities is the degree of `χ`
  have hsum_c : (∑ ψ : ↥(Work.CharCore.Irr ↥P), c ψ) = q ^ k := by
    have hf1 : f 1 = ((∑ ψ : ↥(Work.CharCore.Irr ↥P), c ψ : ℕ) : ℂ) := by
      rw [hc]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_congr rfl (fun ψ _ => by rw [hdeg ψ.1 ψ.2, mul_one])]
      exact (Nat.cast_sum Finset.univ c).symm
    have hf1' : f 1 = ((q ^ k : ℕ) : ℂ) := by
      have h1 : f 1 = χ 1 := by simp [f]
      rw [h1, Work.CharCore.irrDeg_spec hχ, hk]
    exact Nat.cast_injective (hf1.symm.trans hf1')
  -- the norm of `f` is the sum of the squares of the multiplicities
  have hnorm : Work.CharCore.cfInner f f
      = ((∑ ψ : ↥(Work.CharCore.Irr ↥P), (c ψ) ^ 2 : ℕ) : ℂ) := by
    have hsq := Work.CharCore.cfInner_eq_sum_sq (G := ↥P) (s := Work.CharCore.Irr ↥P)
      (fun _ hx => hx) (fun ψ => (c ψ : ℤ))
    have hcoe : (∑ ψ : ↥(Work.CharCore.Irr ↥P), (((c ψ : ℤ)) : ℂ) • (ψ : ↥P → ℂ)) = f := by
      rw [hc]
      refine Finset.sum_congr rfl (fun ψ _ => ?_)
      simp
    rw [hcoe] at hsq
    rw [hsq]
    push_cast
    ring
  -- the counting identity, turned into an identity between natural numbers
  have hSQ : p * (∑ ψ : ↥(Work.CharCore.Irr ↥P), (c ψ) ^ 2)
      = (Work.CharCore.irrDeg χ) ^ 2 + (p - 1) := by
    have hcf : Work.CharCore.cfInner f f
        = (Fintype.card ↥P : ℂ)⁻¹ * ((∑ s : ↥P, Complex.normSq (f s)) : ℂ) := by
      rw [Work.CharCore.cfInner_apply]
      congr 1
      have hstep : (∑ s : ↥P, f s * starRingEnd ℂ (f s))
          = ∑ s : ↥P, ((Complex.normSq (f s)) : ℂ) :=
        Finset.sum_congr rfl (fun s _ => Complex.mul_conj (f s))
      rw [hstep]
    have hcardP : (Fintype.card ↥P : ℂ) = (p : ℂ) := by
      rw [Fintype.card_eq_nat_card, hPcard]
    have hcount' : (∑ s : ↥P, Complex.normSq (f s))
        = (Work.CharCore.irrDeg χ : ℝ) ^ 2 + ((p : ℝ) - 1) := hcount
    have hsumN : (∑ s : ↥P, ((Complex.normSq (f s)) : ℂ))
        = ((((Work.CharCore.irrDeg χ : ℝ) ^ 2 + ((p : ℝ) - 1)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sum, hcount']
    have hmain : (((∑ ψ : ↥(Work.CharCore.Irr ↥P), (c ψ) ^ 2 : ℕ)) : ℂ)
        = (p : ℂ)⁻¹ * ((((Work.CharCore.irrDeg χ : ℝ) ^ 2 + ((p : ℝ) - 1)) : ℝ) : ℂ) := by
      rw [← hnorm, hcf, hcardP, hsumN]
    have hpne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hcast : (((p * ∑ ψ : ↥(Work.CharCore.Irr ↥P), (c ψ) ^ 2 : ℕ)) : ℂ)
        = (((Work.CharCore.irrDeg χ) ^ 2 + (p - 1) : ℕ) : ℂ) := by
      rw [Nat.cast_mul, hmain, ← mul_assoc, mul_inv_cancel₀ hpne, one_mul]
      push_cast [Nat.cast_sub hp.one_le]
      ring
    exact Nat.cast_injective hcast
  -- the arithmetic hypotheses on the multiplicities
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact absurd (by rw [hk, h]; norm_num) hne1
    · exact h
  let n : ↥(Work.CharCore.Irr ↥P) → ℤ := fun ψ => (c ψ : ℤ)
  have hnn : ∀ ψ, 0 ≤ n ψ := fun ψ => Int.natCast_nonneg _
  have hsum_n : (∑ ψ : ↥(Work.CharCore.Irr ↥P), n ψ) = (q : ℤ) ^ k := by
    have h1 : (∑ ψ : ↥(Work.CharCore.Irr ↥P), ((c ψ : ℕ) : ℤ)) = (((q ^ k : ℕ)) : ℤ) := by
      rw [← hsum_c]; push_cast; ring
    have h2 : (((q ^ k : ℕ)) : ℤ) = (q : ℤ) ^ k := by push_cast; ring
    rw [show n = fun ψ => ((c ψ : ℕ) : ℤ) from rfl, h1, h2]
  have hdual : (∑ ψ : ↥(Work.CharCore.Irr ↥P), ∑ ψ' : ↥(Work.CharCore.Irr ↥P),
      (n ψ - n ψ') ^ 2) = 2 * ((p : ℤ) - 1) := by
    rw [sum_pair_sq_eq n]
    have hSZ : (∑ ψ : ↥(Work.CharCore.Irr ↥P), (n ψ) ^ 2)
        = (((∑ ψ : ↥(Work.CharCore.Irr ↥P), (c ψ) ^ 2 : ℕ)) : ℤ) := by
      show (∑ ψ, (((c ψ : ℕ) : ℤ)) ^ 2) = _
      push_cast
      ring
    have hDZ : (∑ ψ : ↥(Work.CharCore.Irr ↥P), n ψ) = ((q ^ k : ℕ) : ℤ) := by
      rw [hsum_n]
      push_cast
      ring
    have hkey : (Fintype.card ↥(Work.CharCore.Irr ↥P) : ℤ)
          * (∑ ψ : ↥(Work.CharCore.Irr ↥P), (n ψ) ^ 2)
          - (∑ ψ : ↥(Work.CharCore.Irr ↥P), n ψ) ^ 2 = (p : ℤ) - 1 := by
      rw [hcard_irr, hSZ, hDZ]
      have hSQZ : (p : ℤ) * (((∑ ψ : ↥(Work.CharCore.Irr ↥P), (c ψ) ^ 2 : ℕ)) : ℤ)
          = ((((Work.CharCore.irrDeg χ) ^ 2 + (p - 1) : ℕ)) : ℤ) := by
        rw [← hSQ]
        push_cast
        ring
      rw [hSQZ]
      have hdq : ((Work.CharCore.irrDeg χ : ℕ) : ℤ) = ((q ^ k : ℕ) : ℤ) := by rw [hk]
      push_cast [Nat.cast_sub hp.one_le, hdq]
      ring
    rw [hkey]
  -- the arithmetic core: no multiplicity vanishes
  have hfin : ∀ ψ : ↥(Work.CharCore.Irr ↥P), c ψ ≠ 0 := by
    intro ψ
    have h := arith_final (ι := ↥(Work.CharCore.Irr ↥P)) (m := k) (n := n)
      hp hcard_irr hq hqodd hk1 hnn hsum_n hdual ψ
    exact fun hc0 => h (by simp [n, hc0])
  -- the sum of `χ` over `P` is `p` times the multiplicity of the trivial character
  have hpsi0 : (fun _ : ↥P => (1 : ℂ)) ∈ Work.CharCore.Irr ↥P :=
    Work.CharCore.principalChar_mem_Irr
  have hcf_psi0 : Work.CharCore.cfInner f (fun _ : ↥P => (1 : ℂ))
      = (c ⟨fun _ => (1 : ℂ), hpsi0⟩ : ℂ) := by
    rw [hc, Work.CharCore.cfInner_sum_smul_left]
    rw [Finset.sum_eq_single (⟨fun _ : ↥P => (1 : ℂ), hpsi0⟩ : ↥(Work.CharCore.Irr ↥P))]
    · rw [Work.CharCore.irr_orthonormal (fun _ : ↥P => (1 : ℂ)) (fun _ : ↥P => (1 : ℂ))
        hpsi0 hpsi0]
      simp
    · intro b _ hb
      rw [Work.CharCore.irr_orthonormal (b : ↥P → ℂ) (fun _ : ↥P => (1 : ℂ)) b.2 hpsi0]
      have hne : ¬ ((b : ↥P → ℂ) = (fun _ : ↥P => (1 : ℂ))) :=
        fun h => hb (Subtype.ext h)
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hsum_cf : Work.CharCore.cfInner f (fun _ : ↥P => (1 : ℂ))
      = (Fintype.card ↥P : ℂ)⁻¹ * ∑ s : ↥P, f s := by
    rw [Work.CharCore.cfInner_apply]
    congr 1
    refine Finset.sum_congr rfl (fun s _ => ?_)
    show f s * starRingEnd ℂ ((fun _ : ↥P => (1 : ℂ)) s) = f s
    simp
  have hgoal : (∑ s : ↥P, χ (s : G))
      = (((p * c ⟨fun _ => (1 : ℂ), hpsi0⟩ : ℕ)) : ℂ) := by
    have hcardP : (Fintype.card ↥P : ℂ) = (p : ℂ) := by
      rw [Fintype.card_eq_nat_card, hPcard]
    have hpne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have h1 : (∑ s : ↥P, f s) = (p : ℂ) * (c ⟨fun _ => (1 : ℂ), hpsi0⟩ : ℂ) := by
      have h2 : (c ⟨fun _ => (1 : ℂ), hpsi0⟩ : ℂ)
          = (p : ℂ)⁻¹ * ∑ s : ↥P, f s := by
        rw [← hcf_psi0, hsum_cf, hcardP]
      have h3 := congrArg (fun z : ℂ => (p : ℂ) * z) h2
      rw [← mul_assoc, mul_inv_cancel₀ hpne, one_mul] at h3
      exact h3.symm
    rw [show (∑ s : ↥P, χ (s : G)) = ∑ s : ↥P, f s from rfl, h1]
    push_cast
    ring
  rw [hgoal]
  exact Nat.cast_ne_zero.mpr (Nat.mul_pos hp.pos (Nat.pos_of_ne_zero (hfin _))).ne'

end Work.Hering.AppVII
