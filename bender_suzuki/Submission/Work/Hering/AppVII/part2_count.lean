import Mathlib
import Submission.Work.Clifford.All
import Submission.Work.CharCore.Main
import Submission.Work.PGroup.Basic
import Submission.Work.Hering.AppVII.part2_orbitSum_norm
import Submission.Work.Hering.AppVII.part2_sum_bijection
import Submission.Work.Hering.AppVII.part2_count_irrNorm
import Submission.Work.Hering.AppVII.part2_count_resNorm
import Submission.Work.Hering.AppVII.part2_count_cardCompl

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.AppVII

theorem part2_count {H : Type*} [Group H] [Fintype H] {p : ℕ} (Q P : Subgroup H) [Fintype ↥P]
    (hQn : Q.Normal) (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = ⊤) (hPcard : Nat.card ↥P = p)
    {χ : H → ℂ} (hχ : χ ∈ Work.CharCore.Irr H)
    {θ : ↥Q → ℂ} (hθ : θ ∈ Work.Clifford.Irr ↥Q) {e : ℕ} (he : 0 < e)
    (hres : Work.Clifford.resFun Q χ = (e : ℂ) • Work.Clifford.orbitSum Q θ)
    (hcoset : ∀ (s : ↥P), s ≠ 1 → ∀ u : ↥Q,
      Complex.normSq (χ ((u : H) * (s : H))) = Complex.normSq (χ (s : H))) :
    ∑ s : ↥P, Complex.normSq (χ (s : H))
      = (Work.CharCore.irrDeg χ : ℝ) ^ 2
        + ((p : ℝ) - (e : ℝ) ^ 2 * (((Work.Clifford.charOrbit Q θ).card : ℕ) : ℝ)) := by
  classical
  haveI : Fintype ↥Q := inferInstance
  -- (1) first orthogonality relation for the irreducible character `χ`
  have hH : (∑ y : H, Complex.normSq (χ y)) = (Nat.card H : ℝ) :=
    part2_count_irrNorm hχ
  -- (2) reindex the sum over `H = Q ⋊ P` as a double sum over the cosets `Q · s`
  have hreindex : (∑ y : H, Complex.normSq (χ y))
      = ∑ s : ↥P, ∑ u : ↥Q, Complex.normSq (χ ((u : H) * (s : H))) :=
    part2_sum_bijection Q P hQn hinf hsup (fun y => Complex.normSq (χ y))
  -- (3) the coset at `s = 1`: `∑_{u ∈ Q} |χ u|² = e² · |orbit| · |Q|`
  have hinner_one : (∑ u : ↥Q, Complex.normSq (χ ((u : H) * ((1 : ↥P) : H))))
      = (Nat.card ↥Q : ℝ) * ((e : ℝ) ^ 2 * ((Work.Clifford.charOrbit Q θ).card : ℝ)) := by
    have h1 : (∑ u : ↥Q, Complex.normSq (χ ((u : H) * ((1 : ↥P) : H))))
        = ∑ u : ↥Q, Complex.normSq (χ (u : H)) := by
      apply Finset.sum_congr rfl
      intro u _
      simp
    rw [h1, part2_count_resNorm (G := H) (N := Q) hθ hres]
    ring
  -- (4) a coset at `s ≠ 1`: `|χ|` is constant along `Q · s`
  have hinner_ne : ∀ s : ↥P, s ≠ 1 →
      (∑ u : ↥Q, Complex.normSq (χ ((u : H) * (s : H))))
        = (Nat.card ↥Q : ℝ) * Complex.normSq (χ (s : H)) := by
    intro s hs
    calc ∑ u : ↥Q, Complex.normSq (χ ((u : H) * (s : H)))
        = ∑ _u : ↥Q, Complex.normSq (χ (s : H)) :=
          Finset.sum_congr rfl (fun u _ => hcoset s hs u)
      _ = (Fintype.card ↥Q : ℝ) * Complex.normSq (χ (s : H)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (Nat.card ↥Q : ℝ) * Complex.normSq (χ (s : H)) := by
          rw [Fintype.card_eq_nat_card]
  -- (5) split the outer sum into the `s = 1` term and the rest
  have hsplit : (∑ s : ↥P, ∑ u : ↥Q, Complex.normSq (χ ((u : H) * (s : H))))
      = (∑ u : ↥Q, Complex.normSq (χ ((u : H) * ((1 : ↥P) : H))))
        + ∑ s ∈ Finset.univ.erase (1 : ↥P),
            (∑ u : ↥Q, Complex.normSq (χ ((u : H) * (s : H)))) :=
    (Finset.add_sum_erase Finset.univ
      (fun s : ↥P => ∑ u : ↥Q, Complex.normSq (χ ((u : H) * (s : H))))
      (Finset.mem_univ _)).symm
  have hErase : (∑ s ∈ Finset.univ.erase (1 : ↥P),
        (∑ u : ↥Q, Complex.normSq (χ ((u : H) * (s : H)))))
      = (Nat.card ↥Q : ℝ) *
          ((∑ s : ↥P, Complex.normSq (χ (s : H))) - Complex.normSq (χ (1 : H))) := by
    have h1 : (∑ s ∈ Finset.univ.erase (1 : ↥P),
          (∑ u : ↥Q, Complex.normSq (χ ((u : H) * (s : H)))))
        = ∑ s ∈ Finset.univ.erase (1 : ↥P),
            ((Nat.card ↥Q : ℝ) * Complex.normSq (χ (s : H))) :=
      Finset.sum_congr rfl (fun s hs => hinner_ne s (Finset.mem_erase.mp hs).1)
    rw [h1, ← Finset.mul_sum]
    congr 1
    have h2 := Finset.sum_erase_add Finset.univ (fun s : ↥P => Complex.normSq (χ (s : H)))
      (Finset.mem_univ (1 : ↥P))
    have h2' : (∑ x ∈ Finset.univ.erase (1 : ↥P), Complex.normSq (χ (x : H)))
        + Complex.normSq (χ (1 : H)) = ∑ x : ↥P, Complex.normSq (χ (x : H)) := h2
    linarith [h2']
  -- (6) combine with the order formula `|H| = |Q| · |P|`, cancel `|Q|`
  have hchain : (Nat.card H : ℝ)
      = (Nat.card ↥Q : ℝ) * ((e : ℝ) ^ 2 * ((Work.Clifford.charOrbit Q θ).card : ℝ))
        + (Nat.card ↥Q : ℝ)
          * ((∑ s : ↥P, Complex.normSq (χ (s : H))) - Complex.normSq (χ (1 : H))) := by
    rw [← hH, hreindex, hsplit, hinner_one, hErase]
  have hL3 : (Nat.card H : ℝ) = (Nat.card ↥Q : ℝ) * (Nat.card ↥P : ℝ) := by
    exact_mod_cast part2_count_cardCompl Q P hQn hinf hsup
  have hcancel : (e : ℝ) ^ 2 * ((Work.Clifford.charOrbit Q θ).card : ℝ)
        + ((∑ s : ↥P, Complex.normSq (χ (s : H))) - Complex.normSq (χ (1 : H)))
      = (Nat.card ↥P : ℝ) := by
    have hcQnz : (Nat.card ↥Q : ℝ) ≠ 0 := by
      rw [← Fintype.card_eq_nat_card]
      exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(1 : ↥Q)⟩).ne'
    have hsum := hchain.symm.trans hL3
    have h2 : (Nat.card ↥Q : ℝ)
          * ((e : ℝ) ^ 2 * ((Work.Clifford.charOrbit Q θ).card : ℝ)
              + ((∑ s : ↥P, Complex.normSq (χ (s : H))) - Complex.normSq (χ (1 : H))))
        = (Nat.card ↥Q : ℝ) * (Nat.card ↥P : ℝ) := by
      rw [mul_add]
      exact hsum
    exact mul_left_cancel₀ hcQnz h2
  -- (7) evaluate at `1` and finish
  have hN1 : Complex.normSq (χ (1 : H)) = (Work.CharCore.irrDeg χ : ℝ) ^ 2 := by
    rw [Work.CharCore.irrDeg_spec hχ, Complex.normSq_natCast]
    ring
  have hp : (Nat.card ↥P : ℝ) = (p : ℝ) := by exact_mod_cast hPcard
  nlinarith [hcancel, hN1, hp]

end Work.Hering.AppVII
