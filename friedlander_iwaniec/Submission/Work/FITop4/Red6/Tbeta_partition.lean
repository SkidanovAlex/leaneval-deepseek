import Mathlib
import Submission.Work.FITop4.Defs6
import Submission.Work.FITop4.Areas6
import Submission.Work.FIArea2.G0_fix
import Submission.Work.FIArea7.ReSymbolTwist
import Submission.Work.FIArea2.isCoprime_star_of_squarefree_odd_gnorm
import Submission.Work.FITop4.Red6.G0_eq_ratioSym_sum

/-!
# `Submission.Work.FITop4.Red6.Tbeta_partition`

The bookkeeping identity of *FI* (10.5) = (10.13): the main term `T(β)` on the *corrected*
kernel `G₀ = Cnt/|Δ|` (`Work.FIArea2.G0fix`) is the cut-`1` member of the family `T_cut(β)`, and
the four cuts (10.15)–(10.17) plus the boundary `4dX = |Δ|` partition the `d`-range
`{d : 4d ∣ |Δ(z₁,z₂)|}`.  Hence

  `T(β) = U(β) + V(β) + W(β) + B(β)`.

Unlike the frozen round-3/round-4 statement (`Work.FITop3.Assembly.Tbeta_partition`), the
identity is *not* definitional here: `G₀` is the count (6.12) divided by `|Δ|`, and the equality
`G₀(z₁,z₂) = 2∑_{4d|Δ}(φ(d)/d)(z₂/z₁|d)` is Lemma 8.4 / (8.16), supplied by
`Work.FIArea2.Cnt_eq_two_sum_of_primitive` on the support of the coefficient (which gives
primitivity, odd squarefree norms, `z₁ ≡ z₂ (mod 8)`, coprimality and `Δ ≠ 0`) — packaged here as
`betaCoeff_G0_eq_ratioSym_sum`.  The remaining bookkeeping is formal: every `d` in
`{d : 4d ∣ |Δ|}` falls into exactly one of `d ≤ X`, `X < d ∧ 4dX < |Δ|`, `X < d ∧ 4dX > |Δ|`,
`X < d ∧ 4dX = |Δ|`.
-/

namespace Work.FITop4.Red6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

set_option linter.style.haveILetI false

noncomputable section

/-! ## 1. The (8.16) identity on the support of a coefficient -/

/-- **`G₀` is the (8.16) sum with *FI*'s ratio symbol**, at two nonzero points of the support of a
coefficient of (4.13)+(5.13)+(5.7) that are coprime.  All the side conditions of Lemma 8.4 —
`z₁` of odd norm, `z₁ ≡ z₂ (mod 8)`, `Δ ≠ 0`, primitivity, `(|z₁|²,|Δ|) = 1` — are read off the
support of `IsBetaCoeff6` and fed to `G0_eq_ratioSym_sum`. -/
lemma betaCoeff_G0_eq_ratioSym_sum {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z1 z2 : GaussianInt}
    (h1 : β z1 ≠ 0) (h2 : β z2 ≠ 0) (hcop : Work.FIPlan.GaussCoprime z1 z2) :
    Work.FITop4.G0 z1 z2
      = 2 * ∑ d ∈ Work.FITop4.Sset z1 z2,
          ((Nat.totient d : ℝ) / (d : ℝ)) * (Work.FIArea7.ratioSym z1 z2 d : ℝ) := by
  have hbox1 := Work.FITop4.IsBetaCoeff6.support hβ h1
  have hbox2 := Work.FITop4.IsBetaCoeff6.support hβ h2
  have hodd1 : Odd (Work.FIPlan.gnorm z1) := Work.FIArea2.InPolarBox.odd_gnorm hbox1
  have hodd2 : Odd (Work.FIPlan.gnorm z2) := Work.FIArea2.InPolarBox.odd_gnorm hbox2
  have hprim1 : IsCoprime z1 (star z1) :=
    Work.FIArea2.isCoprime_star_of_squarefree_odd_gnorm
      (Work.FITop4.IsBetaCoeff6.squarefree_gnorm hβ h1) hodd1
  have hprim2 : IsCoprime z2 (star z2) :=
    Work.FIArea2.isCoprime_star_of_squarefree_odd_gnorm
      (Work.FITop4.IsBetaCoeff6.squarefree_gnorm hβ h2) hodd2
  have hNlt : (1 : ℝ) < (Work.FIPlan.gnorm z1 : ℝ) :=
    lt_of_le_of_lt Pa.hN1 (Work.FIArea2.InPolarBox.norm_bounds hbox1).1
  have hnorm2 : 2 ≤ Work.FIPlan.gnorm z1 := by
    have h1' : (1 : ℕ) < Work.FIPlan.gnorm z1 := by exact_mod_cast hNlt
    omega
  have hD0 : Work.FIPlan.Delta z1 z2 ≠ 0 :=
    Work.FIArea2.Delta_ne_zero_of_coprime hcop hprim1 hprim2 hnorm2
  have hD : Work.FIPlan.absDelta z1 z2 ≠ 0 := by
    rw [Work.FIPlan.absDelta]
    exact fun h => hD0 (Int.natAbs_eq_zero.mp h)
  exact G0_eq_ratioSym_sum hodd1 (Work.FITop4.IsBetaCoeff6.sameClass hβ h1 h2) hD hcop hprim1 hprim2

/-! ## 2. The weight attached to a modulus `d` -/

/-- The modulus weight `(φ(d)/d)·(z₂/z₁|d)·log 2|z₁z₂/Δ|` of (10.13). -/
private def Pc (z1 z2 : GaussianInt) (d : ℕ) : ℝ :=
  ((Nat.totient d : ℝ) / (d : ℝ)) * (Work.FIArea7.ratioSym z1 z2 d : ℝ)
    * Work.FITop4.logFac6 z1 z2

/-- The `log`-free part `∑_{4d ∣ Δ} (φ(d)/d)(z₂/z₁|d)` of (8.16), so that `G₀ = 2 Qc`. -/
private def Qc (z1 z2 : GaussianInt) : ℝ :=
  ∑ d ∈ Work.FITop4.Sset z1 z2,
    ((Nat.totient d : ℝ) / (d : ℝ)) * (Work.FIArea7.ratioSym z1 z2 d : ℝ)

/-- The common outer shape of `T`, `U`, `V`, `W`, `B`: a double sum over `gBox Rz`, restricted to
coprime pairs, of `β z₁ β̄ z₂` times a weight `w`. -/
private def Ksum (Rz : ℤ) (β : GaussianInt → ℂ) (w : GaussianInt → GaussianInt → ℂ) : ℂ :=
  ∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
    (if Work.FIPlan.GaussCoprime z1 z2 then β z1 * star (β z2) * w z1 z2 else 0)

/-! ## 3. The four cut functions of (10.15)–(10.17) and the boundary -/

private def cutU (X : ℕ) : GaussianInt → GaussianInt → ℕ → ℝ :=
  fun _ _ d => if d ≤ X then (1 : ℝ) else 0

private def cutV (X : ℕ) : GaussianInt → GaussianInt → ℕ → ℝ :=
  fun z1 z2 d =>
    if X < d ∧ 4 * d * X < Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0

private def cutW (X : ℕ) : GaussianInt → GaussianInt → ℕ → ℝ :=
  fun z1 z2 d =>
    if X < d ∧ 4 * d * X > Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0

private def cutB (X : ℕ) : GaussianInt → GaussianInt → ℕ → ℝ :=
  fun z1 z2 d =>
    if X < d ∧ 4 * d * X = Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0

/-! ## 4. The weights of the five sums -/

private def wG : GaussianInt → GaussianInt → ℂ :=
  fun z1 z2 => ((Work.FITop4.G0 z1 z2 * Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ)

private def wU (X : ℕ) : GaussianInt → GaussianInt → ℂ :=
  fun z1 z2 => ∑ d ∈ Work.FITop4.Sset z1 z2,
    (Pc z1 z2 d : ℂ) * (cutU X z1 z2 d : ℂ)

private def wV (X : ℕ) : GaussianInt → GaussianInt → ℂ :=
  fun z1 z2 => ∑ d ∈ Work.FITop4.Sset z1 z2,
    (Pc z1 z2 d : ℂ) * (cutV X z1 z2 d : ℂ)

private def wW (X : ℕ) : GaussianInt → GaussianInt → ℂ :=
  fun z1 z2 => ∑ d ∈ Work.FITop4.Sset z1 z2,
    (Pc z1 z2 d : ℂ) * (cutW X z1 z2 d : ℂ)

private def wB (X : ℕ) : GaussianInt → GaussianInt → ℂ :=
  fun z1 z2 => ∑ d ∈ Work.FITop4.Sset z1 z2,
    (Pc z1 z2 d : ℂ) * (cutB X z1 z2 d : ℂ)

/-! ## 5. Elementary identities -/

/-- The four cut conditions partition the `d`-range: exactly one of `d ≤ X`, `X < d ∧ 4dX < |Δ|`,
`X < d ∧ 4dX > |Δ|`, `X < d ∧ 4dX = |Δ|` holds. -/
private lemma cut_sum_one (X d A : ℕ) :
    (if d ≤ X then (1:ℝ) else 0) + (if X < d ∧ 4*d*X < A then (1:ℝ) else 0)
      + (if X < d ∧ 4*d*X > A then (1:ℝ) else 0)
      + (if X < d ∧ 4*d*X = A then (1:ℝ) else 0) = 1 := by
  by_cases h : d ≤ X
  · have h2' : ¬ (X < d ∧ 4*d*X < A) := by rintro ⟨hh,_⟩; omega
    have h3' : ¬ (X < d ∧ 4*d*X > A) := by rintro ⟨hh,_⟩; omega
    have h4' : ¬ (X < d ∧ 4*d*X = A) := by rintro ⟨hh,_⟩; omega
    simp only [if_pos h, if_neg h2', if_neg h3', if_neg h4']
    norm_num
  · rw [if_neg h]
    have h2 : X < d := by omega
    rcases lt_trichotomy (4*d*X) A with hlt | heq | hgt
    · have hp : X < d ∧ 4*d*X < A := ⟨h2, hlt⟩
      have hn : ¬ (X < d ∧ 4*d*X > A) := by rintro ⟨_, hh⟩; omega
      have hn2 : ¬ (X < d ∧ 4*d*X = A) := by rintro ⟨_, hh⟩; omega
      simp only [if_pos hp, if_neg hn, if_neg hn2]
      norm_num
    · have hp : X < d ∧ 4*d*X = A := ⟨h2, heq⟩
      have hn : ¬ (X < d ∧ 4*d*X < A) := by rintro ⟨_, hh⟩; omega
      have hn2 : ¬ (X < d ∧ 4*d*X > A) := by rintro ⟨_, hh⟩; omega
      simp only [if_neg hn, if_pos hp, if_neg hn2]
      norm_num
    · have hp : X < d ∧ A < 4*d*X := ⟨h2, hgt⟩
      have hn : ¬ (X < d ∧ 4*d*X < A) := by rintro ⟨_, hh⟩; omega
      have hn2 : ¬ (X < d ∧ 4*d*X = A) := by rintro ⟨_, hh⟩; omega
      simp only [if_neg hn, if_neg hn2, if_pos hp]
      norm_num

/-! ## 6. `Ksum` is additive and `ℂ`-linear in its weight -/

private lemma Ksum_add (Rz : ℤ) (β : GaussianInt → ℂ)
    (w1 w2 : GaussianInt → GaussianInt → ℂ) :
    Ksum Rz β (w1 + w2) = Ksum Rz β w1 + Ksum Rz β w2 := by
  simp only [Ksum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro z1 _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro z2 _
  by_cases hg : Work.FIPlan.GaussCoprime z1 z2
  · simp only [hg, if_true, Pi.add_apply]; ring
  · simp only [hg, if_false]; ring

private lemma Ksum_smul (Rz : ℤ) (β : GaussianInt → ℂ) (a : ℂ)
    (w : GaussianInt → GaussianInt → ℂ) :
    Ksum Rz β (a • w) = a * Ksum Rz β w := by
  simp only [Ksum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro z1 _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro z2 _
  by_cases hg : Work.FIPlan.GaussCoprime z1 z2
  · simp only [hg, if_true, Pi.smul_apply, smul_eq_mul]; ring
  · simp only [hg, if_false]; ring

/-! ## 7. The five sums in the common shape -/

/-- `T_cut(β)` expressed through `Ksum`: the inner `d`-sum of (10.13) is `∑_d Pc · cut`. -/
private lemma Tcut_eq (Rz : ℤ) (β : GaussianInt → ℂ)
    (c : GaussianInt → GaussianInt → ℕ → ℝ) :
    Work.FITop4.Tcut Rz c β
      = 2 * Ksum Rz β (fun z1 z2 => ∑ d ∈ Work.FITop4.Sset z1 z2,
          (Pc z1 z2 d : ℂ) * (c z1 z2 d : ℂ)) := by
  simp only [Work.FITop4.Tcut, Ksum]
  congr 1
  apply Finset.sum_congr rfl; intro z1 _
  apply Finset.sum_congr rfl; intro z2 _
  by_cases hg : Work.FIPlan.GaussCoprime z1 z2
  · simp only [hg, if_true]
    congr 1
    apply Finset.sum_congr rfl; intro d _
    simp only [Pc]
    push_cast
    ring
  · simp only [hg, if_false]

/-- `T(β)` in the common shape, with weight `G₀ · log`. -/
private lemma Tbeta_eq_Ksum (Rz : ℤ) (β : GaussianInt → ℂ) :
    Work.FITop4.Tbeta Rz β = Ksum Rz β wG := by
  simp only [Work.FITop4.Tbeta, Ksum, wG]

/-! ## 8. The pointwise partition -/

/-- The partition of the inner `d`-sum: the four cut-weighted sums add up to the uncut one. -/
private lemma h2_aux (X : ℕ) (z1 z2 : GaussianInt) :
    (∑ d ∈ Work.FITop4.Sset z1 z2, (Pc z1 z2 d : ℂ) * (cutU X z1 z2 d : ℂ))
      + (∑ d ∈ Work.FITop4.Sset z1 z2, (Pc z1 z2 d : ℂ) * (cutV X z1 z2 d : ℂ))
      + (∑ d ∈ Work.FITop4.Sset z1 z2, (Pc z1 z2 d : ℂ) * (cutW X z1 z2 d : ℂ))
      + (∑ d ∈ Work.FITop4.Sset z1 z2, (Pc z1 z2 d : ℂ) * (cutB X z1 z2 d : ℂ))
      = ∑ d ∈ Work.FITop4.Sset z1 z2, (Pc z1 z2 d : ℂ) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro d _
  have h := cut_sum_one X d (Work.FIPlan.absDelta z1 z2)
  simp only [cutU, cutV, cutW, cutB] at h ⊢
  rw [← mul_add, ← mul_add, ← mul_add, ← Complex.ofReal_add, ← Complex.ofReal_add,
    ← Complex.ofReal_add, h, Complex.ofReal_one, mul_one]

/-! ## 9. The pointwise `G₀ log = 2 ∑_d Pc` -/

/-- `G₀ · log = 2 ∑_d Pc`, i.e. the middle step of (10.5) `→` (10.13), at a non-zero pair. -/
private lemma wG_eq {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (X : ℕ)
    {z1 z2 : GaussianInt} (hb1 : β z1 ≠ 0) (hb2 : β z2 ≠ 0)
    (hcop : Work.FIPlan.GaussCoprime z1 z2) :
    wG z1 z2 = ((2:ℂ) • wU X + (2:ℂ) • wV X + (2:ℂ) • wW X + (2:ℂ) • wB X) z1 z2 := by
  have hid : Work.FITop4.G0 z1 z2 = 2 * Qc z1 z2 := by
    simpa only [Qc] using betaCoeff_G0_eq_ratioSym_sum hβ hb1 hb2 hcop
  have hGL : ((Work.FITop4.G0 z1 z2 * Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ)
      = 2 * (∑ d ∈ Work.FITop4.Sset z1 z2, (Pc z1 z2 d : ℂ)) := by
    have h1 : (Work.FITop4.G0 z1 z2 * Work.FITop4.logFac6 z1 z2 : ℝ)
        = 2 * (∑ d ∈ Work.FITop4.Sset z1 z2, Pc z1 z2 d) := by
      rw [show (Work.FITop4.G0 z1 z2 * Work.FITop4.logFac6 z1 z2 : ℝ)
            = 2 * (Qc z1 z2 * Work.FITop4.logFac6 z1 z2) by rw [hid]; ring,
          show Qc z1 z2 * Work.FITop4.logFac6 z1 z2
            = ∑ d ∈ Work.FITop4.Sset z1 z2, Pc z1 z2 d by
              simp only [Qc, Pc]; rw [Finset.sum_mul]]
    rw [h1, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_sum]
  have hR : ((2:ℂ) • wU X + (2:ℂ) • wV X + (2:ℂ) • wW X + (2:ℂ) • wB X) z1 z2
      = 2 * (∑ d ∈ Work.FITop4.Sset z1 z2, (Pc z1 z2 d : ℂ)) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, wU, wV, wW, wB]
    rw [← mul_add, ← mul_add, ← mul_add, h2_aux]
  simp only [wG]
  rw [hGL, hR]

/-! ## 10. The partition identity on the whole double sum -/

/-- The partition identity at the level of the double sum: the product `β z₁ β̄ z₂` vanishes
unless both `β z₁` and `β z₂` are non-zero, which is exactly where `wG_eq` applies. -/
private lemma Ksum_wG_eq {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (X : ℕ) (Rz : ℤ) :
    Ksum Rz β wG
      = Ksum Rz β ((2:ℂ) • wU X + (2:ℂ) • wV X + (2:ℂ) • wW X + (2:ℂ) • wB X) := by
  simp only [Ksum]
  apply Finset.sum_congr rfl; intro z1 _
  apply Finset.sum_congr rfl; intro z2 _
  by_cases hcop : Work.FIPlan.GaussCoprime z1 z2
  · simp only [hcop, if_true]
    by_cases hb1 : β z1 = 0
    · simp [hb1]
    · by_cases hb2 : β z2 = 0
      · simp [hb2]
      · rw [wG_eq hβ X hb1 hb2 hcop]
  · simp only [hcop, if_false]

/-! ## 11. The theorem -/

theorem Tbeta_partition {Pa : Work.FITop.Params} (X : ℕ) {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) :
    Work.FITop4.Tbeta (Work.FITop.radN Pa) β
      = Work.FITop4.Ucut (Work.FITop.radN Pa) X β + Work.FITop4.Vcut (Work.FITop.radN Pa) X β
        + Work.FITop4.Wcut (Work.FITop.radN Pa) X β
        + Work.FITop4.Bcut (Work.FITop.radN Pa) X β := by
  have hT : Work.FITop4.Tbeta (Work.FITop.radN Pa) β
      = Ksum (Work.FITop.radN Pa) β wG := Tbeta_eq_Ksum (Work.FITop.radN Pa) β
  have hU : Work.FITop4.Ucut (Work.FITop.radN Pa) X β
      = 2 * Ksum (Work.FITop.radN Pa) β (wU X) :=
    Tcut_eq (Work.FITop.radN Pa) β (cutU X)
  have hV : Work.FITop4.Vcut (Work.FITop.radN Pa) X β
      = 2 * Ksum (Work.FITop.radN Pa) β (wV X) :=
    Tcut_eq (Work.FITop.radN Pa) β (cutV X)
  have hW : Work.FITop4.Wcut (Work.FITop.radN Pa) X β
      = 2 * Ksum (Work.FITop.radN Pa) β (wW X) :=
    Tcut_eq (Work.FITop.radN Pa) β (cutW X)
  have hB : Work.FITop4.Bcut (Work.FITop.radN Pa) X β
      = 2 * Ksum (Work.FITop.radN Pa) β (wB X) :=
    Tcut_eq (Work.FITop.radN Pa) β (cutB X)
  rw [hT, hU, hV, hW, hB]
  rw [← Ksum_smul (Work.FITop.radN Pa) β (2:ℂ) (wU X),
      ← Ksum_smul (Work.FITop.radN Pa) β (2:ℂ) (wV X),
      ← Ksum_smul (Work.FITop.radN Pa) β (2:ℂ) (wW X),
      ← Ksum_smul (Work.FITop.radN Pa) β (2:ℂ) (wB X)]
  rw [← Ksum_add (Work.FITop.radN Pa) β ((2:ℂ) • wU X) ((2:ℂ) • wV X),
      ← Ksum_add (Work.FITop.radN Pa) β ((2:ℂ) • wU X + (2:ℂ) • wV X) ((2:ℂ) • wW X),
      ← Ksum_add (Work.FITop.radN Pa) β
        (((2:ℂ) • wU X + (2:ℂ) • wV X) + (2:ℂ) • wW X) ((2:ℂ) • wB X)]
  exact Ksum_wG_eq hβ X (Work.FITop.radN Pa)

end

end Work.FITop4.Red6
