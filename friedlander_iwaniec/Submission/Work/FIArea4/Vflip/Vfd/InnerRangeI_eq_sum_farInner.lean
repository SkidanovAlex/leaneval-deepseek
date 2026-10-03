import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.farPre
import Submission.Work.FIArea4.Vflip.Vfd.FarSepDefs

/-!
# The `(m,Q₁,Q₂)`-piece of the far sum as a sum over the common divisor `c`

The far sum of the flipped-moduli bound is indexed either by the *unreduced* pair of box points
`z = (q', ((r₁,s₁),(r₂,s₂)))` (giving `InnerRangeI`) or by the *reduced* pair, after the common
divisor `c = (r₁,r₂)` has been extracted (giving `farInner`). This file proves the two descriptions
agree:

`μ(m) · InnerRangeI m Q₁ Q₂ = Σ_{c ≤ 2R} farInner m c Q₁ Q₂`.

The proof fibres `FarIdxI` over the value `c = pairC r₁ r₂`, and on each fibre transports along the
bijection

`z = (q', ((r₁,s₁),(r₂,s₂)))  ↦  ((q',(r₁/c, s₁)),(r₂/c, s₂))`

between the unreduced indices with `pairC r₁ r₂ = c` and the reduced indices of `farSet m c`.  The
per-point identity `μ(m)·(GG·flipWeight) = farCoef·farWeight` is `farRed_value`; the only analytic
input is that the two `bump`-arguments `|x_{pq}|·y` and `(A/q')/D` agree (`bump_arg_eq`), so that the
cast `bump` factors match.
-/

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Reduction of the common divisor -/

/-- `pairC (c r₁) (c r₂) = c` when `(r₁,r₂) = 1` and `c ≠ 0`. -/
lemma pairC_mul_left_of_coprime {c r1 r2 : ℕ} (hc : 0 < c) (hcop : Nat.Coprime r1 r2) :
    pairC (c*r1) (c*r2) = c := by
  simp only [pairC, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]

/-- `pairR (c r₁) (c r₂) = r₁` when `(r₁,r₂) = 1` and `c ≠ 0`. -/
lemma pairR_mul_left_of_coprime {c r1 r2 : ℕ} (hc : 0 < c) (hcop : Nat.Coprime r1 r2) :
    pairR (c*r1) (c*r2) = r1 := by
  rw [pairR, pairC_mul_left_of_coprime hc hcop, Nat.mul_div_cancel_left _ hc]

/-- `pairC (c r₂) (c r₁) = c` when `(r₁,r₂) = 1` and `c ≠ 0`. -/
lemma pairC_mul_right_of_coprime {c r1 r2 : ℕ} (hc : 0 < c) (hcop : Nat.Coprime r1 r2) :
    pairC (c*r2) (c*r1) = c := by
  rw [pairC, Nat.gcd_comm, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]

/-- `pairR (c r₂) (c r₁) = r₂` when `(r₁,r₂) = 1` and `c ≠ 0`. -/
lemma pairR_mul_right_of_coprime {c r1 r2 : ℕ} (hc : 0 < c) (hcop : Nat.Coprime r1 r2) :
    pairR (c*r2) (c*r1) = r2 := by
  rw [pairR, pairC_mul_right_of_coprime hc hcop, Nat.mul_div_cancel_left _ hc]

/-- The equality of `bump`-arguments without the hypothesis `D ≠ 0`: both sides degenerate to `0`
when `D = 0`. -/
lemma bump_arg_eq' {D q' : ℕ} {p q : ℕ×ℕ} (h1 : 0 < p.1) (h2 : 0 < q.1) (hq' : 0 < q')
    (hdvd : q' ∣ pairAbs p.1 q.1 p.2 q.2) :
    |xPair p q| * ((pairC p.1 q.1 : ℝ) * (pairR p.1 q.1 : ℝ) * (pairR q.1 p.1 : ℝ)
        / ((q' * D : ℕ) : ℝ))
      = ((pairAbs p.1 q.1 p.2 q.2 / q' : ℕ) : ℝ) / (D : ℝ) := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD; simp
  · exact bump_arg_eq h1 h2 hq' hD hdvd

/-- **The pointwise identity in reduced coordinates.**  For a reduced index `i = ⟨⟨q',ρ₁,s₁⟩,⟨ρ₂,s₂⟩⟩`
(with `(ρ₁,ρ₂) = 1`), the product `farCoef · farWeight` equals `μ(m)` times the product
`GG · flipWeight` evaluated at the unreduced pair `(cρ₁,s₁)`, `(cρ₂,s₂)`. -/
lemma farCoef_mul_farWeight (D : ℕ) (c q' ρ₁ ρ₂ s₁ s₂ : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) (m : ℕ)
    (hc : 0 < c) (hcop : Nat.Coprime ρ₁ ρ₂) (hq' : 0 < q') (hρ1 : 0 < ρ₁) (hρ2 : 0 < ρ₂)
    (hdvd : q' ∣ pairAbs (c*ρ₁) (c*ρ₂) s₁ s₂) :
    farCoef m c α ⟨⟨q', ρ₁, s₁⟩, ⟨ρ₂, s₂⟩⟩ * farWeight D a b c ⟨⟨q', ρ₁, s₁⟩, ⟨ρ₂, s₂⟩⟩
      = (ArithmeticFunction.moebius m : ℂ) *
        (GG a b α (c*ρ₁, s₁) (c*ρ₂, s₂) * flipWeight D q' (c*ρ₁) s₁ (c*ρ₂) s₂) := by
  have hR1 : pairR (c*ρ₁) (c*ρ₂) = ρ₁ := pairR_mul_left_of_coprime hc hcop
  have hR2 : pairR (c*ρ₂) (c*ρ₁) = ρ₂ := pairR_mul_right_of_coprime hc hcop
  have hC : pairC (c*ρ₁) (c*ρ₂) = c := pairC_mul_left_of_coprime hc hcop
  have hbump := bump_arg_eq' (D:=D) (q':=q') (p:=(c*ρ₁, s₁)) (q:=(c*ρ₂, s₂))
      (Nat.mul_pos hc hρ1) (Nat.mul_pos hc hρ2) hq' hdvd
  rw [hC, hR1, hR2] at hbump
  simp only [Nat.cast_mul] at hbump
  simp only [farCoef, farWeight, GG, flipWeight, flipCoef, xOrig, ySep]
  rw [hbump, hR1, hR2, Complex.ofReal_mul]
  ring

/-! ## The two index types and the reduction maps -/

/-- The index type of the unreduced far piece: `(q', (p, q))`. -/
abbrev FarZ : Type := ℕ × ((ℕ×ℕ) × (ℕ×ℕ))

/-- Reduction of an unreduced index by the common divisor `pairC r₁ r₂`. -/
def farRed (z : FarZ) : FarIx :=
  ((z.1, (pairR z.2.1.1 z.2.2.1, z.2.1.2)), (pairR z.2.2.1 z.2.1.1, z.2.2.2))

/-- Un-reduction of a reduced index by a common divisor `c`. -/
def farUnp (c : ℕ) (i : FarIx) : FarZ :=
  (i.1.1, ((c*i.1.2.1, i.1.2.2), (c*i.2.1, i.2.2)))

/-- `farRed` maps the unreduced far piece into the reduced one, with `c = pairC r₁ r₂`. -/
lemma farRed_mem (D R S m Q1 Q2 : ℕ) (a b : ℝ)
    {z : FarZ} (hz : z ∈ FarIdxI R S m Q1 Q2) :
    farRed z ∈ farSet D R S a b m (pairC z.2.1.1 z.2.2.1) Q1 Q2 := by
  obtain ⟨hQ1, hQ2, hp, hq, hpa, hpc, hpq⟩ := mem_FarIdxI.mp hz
  rw [mem_boxF] at hp hq
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
  obtain ⟨hq1, hq2, hq3, hq4⟩ := hq
  rw [mem_farSet, farCond]
  simp only [farRed]
  have hp1pos : 0 < z.2.1.1 := by omega
  have hρ1 : pairR z.2.1.1 z.2.2.1 ≤ 2*R := le_trans (Nat.div_le_self _ _) hp2
  have hρ2 : pairR z.2.2.1 z.2.1.1 ≤ 2*R := le_trans (Nat.div_le_self _ _) hq2
  refine ⟨hQ1, hQ2, ?_, ?_, ?_, ?_, hQ2, ?_⟩
  · omega
  · omega
  · omega
  · omega
  · refine ⟨Nat.gcd_pos_of_pos_left _ hp1pos, ?_, ?_, ?_, ?_, ?_, hp3, hp4, hq3, hq4, hpc, ?_⟩
    · have h := Nat.coprime_div_gcd_div_gcd (m := z.2.1.1) (n := z.2.2.1)
        (Nat.gcd_pos_of_pos_left _ hp1pos)
      simpa only [pairC, pairR, Nat.gcd_comm z.2.2.1 z.2.1.1] using h
    · rw [pairC_mul_pairR_left]; exact hp1
    · rw [pairC_mul_pairR_left]; exact hp2
    · rw [pairC_mul_pairR_right]; exact hq1
    · rw [pairC_mul_pairR_right]; exact hq2
    · rw [iAbs, pairC_mul_pairR_left, pairC_mul_pairR_right]; exact hpq

/-- `farUnp` maps the reduced `(m,c,Q)`-piece (cut down to positive `iAbs`) into the unreduced
far piece. -/
lemma farUnp_mem (D R S m Q1 Q2 c : ℕ) (a b : ℝ)
    {i : FarIx} (hi : i ∈ farSet D R S a b m c Q1 Q2) (hpos : 0 < iAbs c i) :
    farUnp c i ∈ FarIdxI R S m Q1 Q2 := by
  obtain ⟨hQ1, hQ2, hr1, hs1, hr2, hs2, hQ2', hfar⟩ := mem_farSet.mp hi
  obtain ⟨hc, hcop, ha1, ha2, hb1, hb2, hd1, hd2, he1, he2, hmc, hmq⟩ := hfar
  rw [mem_FarIdxI]
  simp only [farUnp]
  refine ⟨hQ1, hQ2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_boxF]; exact ⟨ha1, ha2, hd1, hd2⟩
  · rw [mem_boxF]; exact ⟨hb1, hb2, he1, he2⟩
  · exact hpos
  · rw [pairC_mul_left_of_coprime hc hcop]; exact hmc
  · exact hmq

/-- The un-reduction of a reduced index has common divisor `c`. -/
lemma farUnp_pairC (D R S m Q1 Q2 c : ℕ) (a b : ℝ)
    {i : FarIx} (hi : i ∈ farSet D R S a b m c Q1 Q2) :
    pairC (farUnp c i).2.1.1 (farUnp c i).2.2.1 = c := by
  obtain ⟨-, -, -, -, -, -, -, hfar⟩ := mem_farSet.mp hi
  obtain ⟨hc, hcop, -⟩ := hfar
  simp only [farUnp, pairC_mul_left_of_coprime hc hcop]

/-- `farUnp` is a left inverse of `farRed`. -/
lemma farUnp_farRed (z : FarZ) :
    farUnp (pairC z.2.1.1 z.2.2.1) (farRed z) = z := by
  simp only [farUnp, farRed, pairC_mul_pairR_left, pairC_mul_pairR_right]

/-- `farRed` is a left inverse of `farUnp` on reduced pairs. -/
lemma farRed_farUnp {c : ℕ} {i : FarIx} (hc : 0 < c) (hcop : Nat.Coprime i.1.2.1 i.2.1) :
    farRed (farUnp c i) = i := by
  simp only [farRed, farUnp]
  rw [pairR_mul_left_of_coprime hc hcop, pairR_mul_right_of_coprime hc hcop]

/-- **The pointwise identity for an unreduced index.** -/
lemma farRed_value (D R S : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) (m Q1 Q2 : ℕ)
    {z : FarZ} (hz : z ∈ FarIdxI R S m Q1 Q2) :
    (ArithmeticFunction.moebius m : ℂ) * (GG a b α z.2.1 z.2.2
        * flipWeight D z.1 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2)
      = farCoef m (pairC z.2.1.1 z.2.2.1) α (farRed z)
          * farWeight D a b (pairC z.2.1.1 z.2.2.1) (farRed z) := by
  obtain ⟨hQ1, hQ2, hp, hq, hpa, hpc, hpq⟩ := mem_FarIdxI.mp hz
  rw [mem_boxF] at hp hq
  have hp1pos : 0 < z.2.1.1 := by omega
  have hq1pos : 0 < z.2.2.1 := by omega
  have hc : 0 < pairC z.2.1.1 z.2.2.1 := Nat.gcd_pos_of_pos_left _ hp1pos
  have hcop : Nat.Coprime (pairR z.2.1.1 z.2.2.1) (pairR z.2.2.1 z.2.1.1) := by
    have := Nat.coprime_div_gcd_div_gcd (m := z.2.1.1) (n := z.2.2.1)
      (Nat.gcd_pos_of_pos_left _ hp1pos)
    simpa only [pairC, pairR, Nat.gcd_comm z.2.2.1 z.2.1.1] using this
  have hq' : 0 < z.1 := by omega
  have hρ1 : 0 < pairR z.2.1.1 z.2.2.1 := by
    rw [pairR]; exact Nat.div_pos (Nat.gcd_le_left _ hp1pos) (Nat.gcd_pos_of_pos_left _ hp1pos)
  have hρ2 : 0 < pairR z.2.2.1 z.2.1.1 := by
    rw [pairR]; exact Nat.div_pos (Nat.gcd_le_left _ hq1pos) (Nat.gcd_pos_of_pos_left _ hq1pos)
  have hdvd : z.1 ∣ pairAbs (pairC z.2.1.1 z.2.2.1 * pairR z.2.1.1 z.2.2.1)
      (pairC z.2.1.1 z.2.2.1 * pairR z.2.2.1 z.2.1.1) z.2.1.2 z.2.2.2 := by
    rw [pairC_mul_pairR_left, pairC_mul_pairR_right]
    exact dvd_trans (Nat.dvd_mul_left z.1 m) hpq
  rw [show farRed z =
      ((z.1, (pairR z.2.1.1 z.2.2.1, z.2.1.2)), (pairR z.2.2.1 z.2.1.1, z.2.2.2)) from rfl]
  rw [farCoef_mul_farWeight D (pairC z.2.1.1 z.2.2.1) z.1 (pairR z.2.1.1 z.2.2.1)
      (pairR z.2.2.1 z.2.1.1) z.2.1.2 z.2.2.2 a b α m hc hcop hq' hρ1 hρ2 hdvd]
  rw [pairC_mul_pairR_left z.2.1.1 z.2.2.1, pairC_mul_pairR_right z.2.1.1 z.2.2.1]

/-! ## The `iAbs = 0` indices are invisible to `farInner` -/

lemma bump_eq_zero_of_nonpos {y : ℝ} (hy : y ≤ 0) : Work.FIArea4.Vflip.bump y = 0 := by
  rw [Work.FIArea4.Vflip.bump, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

/-- A reduced index with `iAbs = 0` has `xOrig = 0`, hence vanishing `bump`-weight. -/
lemma farCoef_mul_farWeight_eq_zero (D R S m c Q1 Q2 : ℕ) (a b : ℝ) {α : ℕ → ℕ → ℂ}
    {i : FarIx} (hi : i ∈ farSet D R S a b m c Q1 Q2) (h0 : iAbs c i = 0) :
    farCoef m c α i * farWeight D a b c i = 0 := by
  obtain ⟨-, -, -, -, -, -, -, hfar⟩ := mem_farSet.mp hi
  have hpos := farCond_pos hfar
  obtain ⟨hρ1, hρ2⟩ := hpos.2
  obtain ⟨hc, -, -⟩ := hfar
  have hx : xOrig c i = 0 := by
    rw [xOrig]
    refine (xPair_eq_zero_iff (c*i.1.2.1) i.1.2.2 (c*i.2.1) i.2.2
      (Nat.mul_pos hc hρ1) (Nat.mul_pos hc hρ2)).mpr ?_
    rw [← h0]; rfl
  rw [farWeight]
  have hb : Work.FIArea4.Vflip.bump (|xOrig c i| * ySep c D i) = 0 := by
    rw [hx, abs_zero, zero_mul]
    exact bump_eq_zero_of_nonpos le_rfl
  rw [hb, zero_mul, Complex.ofReal_zero, mul_zero]

/-! ## The per-fibre bijection -/

/-- The fibre of `FarIdxI` over the common divisor `c` is the reduced index set `farSet m c`
(cut down to `iAbs ≠ 0`), with matching summands. -/
lemma inner_fiber_eq (D R S : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) (m c Q1 Q2 : ℕ) :
    (∑ z ∈ (FarIdxI R S m Q1 Q2).filter (fun z => pairC z.2.1.1 z.2.2.1 = c),
        (ArithmeticFunction.moebius m : ℂ) * (GG a b α z.2.1 z.2.2
          * flipWeight D z.1 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2))
      = ∑ i ∈ (farSet D R S a b m c Q1 Q2).filter (fun i => 0 < iAbs c i),
          farCoef m c α i * farWeight D a b c i := by
  refine Finset.sum_nbij' (farRed) (farUnp c) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hzI, hzc⟩ := hz
    obtain ⟨-, -, -, -, hpa, -, -⟩ := mem_FarIdxI.mp hzI
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [← hzc]; exact farRed_mem D R S m Q1 Q2 a b hzI
    · rw [← hzc]
      have h1 : iAbs (pairC z.2.1.1 z.2.2.1) (farRed z)
          = pairAbs z.2.1.1 z.2.2.1 z.2.1.2 z.2.2.2 := by
        simp only [iAbs, farRed, pairC_mul_pairR_left, pairC_mul_pairR_right]
      rw [h1]; exact hpa
  · intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨hiS, hipos⟩ := hi
    rw [Finset.mem_filter]
    exact ⟨farUnp_mem D R S m Q1 Q2 c a b hiS hipos, farUnp_pairC D R S m Q1 Q2 c a b hiS⟩
  · intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨-, hzc⟩ := hz
    rw [← hzc]; exact farUnp_farRed z
  · intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨hiS, -⟩ := hi
    obtain ⟨hc, hcop, -⟩ := farCond_of_mem_farSet hiS
    exact farRed_farUnp hc hcop
  · intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hzI, hzc⟩ := hz
    rw [← hzc]; exact farRed_value D R S a b α m Q1 Q2 hzI

/-- Removing the invisible indices (`iAbs = 0`) from `farInner` leaves it unchanged. -/
lemma farInner_eq_filter (D R S : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) (m c Q1 Q2 : ℕ) :
    farInner D R S a b α m c Q1 Q2
      = ∑ i ∈ (farSet D R S a b m c Q1 Q2).filter (fun i => 0 < iAbs c i),
          farCoef m c α i * farWeight D a b c i := by
  rw [farInner]
  exact (Finset.sum_filter_of_ne (fun i hi hne => by
    by_contra hlt
    exact hne (farCoef_mul_farWeight_eq_zero D R S m c Q1 Q2 a b hi
      (Nat.eq_zero_of_not_pos hlt)))).symm

/-! ## The main identity -/

theorem InnerRangeI_eq_sum_farInner (D R S : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) (m Q1 Q2 : ℕ) :
    (ArithmeticFunction.moebius m : ℂ) * InnerRangeI D R S a b α m Q1 Q2
      = ∑ c ∈ Finset.range (2*R+1), farInner D R S a b α m c Q1 Q2 := by
  rw [InnerRangeI, Finset.mul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (s := FarIdxI R S m Q1 Q2)
        (t := Finset.range (2*R+1))
        (g := fun z : FarZ => pairC z.2.1.1 z.2.2.1)
        (fun z hz => Finset.mem_range.mpr (by
          have h := pairC_le_twoR (R:=R) (S:=S) (q:=z.2.2) (mem_FarIdxI.mp hz).2.2.1
          omega))
        (fun z => (ArithmeticFunction.moebius m : ℂ) * (GG a b α z.2.1 z.2.2
          * flipWeight D z.1 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2))]
  exact Finset.sum_congr rfl (fun c _ => by rw [inner_fiber_eq, farInner_eq_filter])

end

end Work.FIArea4.Vflip.Vfd
