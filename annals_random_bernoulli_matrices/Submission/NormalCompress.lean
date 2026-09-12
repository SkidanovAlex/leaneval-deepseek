import Mathlib
import Submission.CompressProp
import Submission.CompressCentered
import Submission.GeoBridge
import Submission.IncompReduction

set_option autoImplicit false
open Matrix MeasureTheory ProbabilityTheory Measure Filter unitInterval
open scoped ENNReal BigOperators

noncomputable section

/-!
# The normal of a shifted Bernoulli matrix is asymptotically incompressible

Tikhomirov 2020, proof of Theorem~A ("Applying Proposition l:compress the
second time"): with the constants produced by Proposition l:compress (both the
`(n−1)×n`-rows version for `s + p ≠ 0` and the centered version for `s = −p`),
the probability that the coordinate function of the random unit normal
`Y_n := nVec(B_n(p) + s·1·1ᵀ)` is `(δ,ν)`-compressible is at most
`(1−p+ε)^n`.  Deterministically: if `Y_n` is `(δ,ν)`-compressible then it is a
witness `x` for the compressible small-ball event of the transposed first-`n−1`
columns, because `Y_n` is orthogonal to each of those columns.
-/

namespace Submission.NormalCompress

universe u

open Submission.GeoBridge (E sqNorm_ofLp_of_unit measureReal_matrix_event_eq_of_ae
  exists_measurable_clamped_matrix emb emb_injective)
open Submission.IncompReduction (nVec shiftMatrix shiftMatrix_apply lastFin nVec_unit
  nVec_orthogonal_emb)
open Submission.NormalVectorMatrix (colVec colVec_coeff)
open Submission.Compress (actSq rowAct)
open Submission.CompressProp (compress_theorem)
open Submission.CompressCentered (compress_theorem_centered)

/-- Deterministic: the row of the transposed-first-columns family applied to
the coordinate function of the unit normal of `shiftMatrix s M` vanishes. -/
lemma rowAct_W_yfn_eq_zero {n : ℕ} (hn : 1 ≤ n) (M : Matrix (Fin n) (Fin n) ℝ) (s : ℝ)
    (k : Fin (n - 1)) :
    (∑ j : Fin n, (shiftMatrix s M) j (emb k) * ((nVec (shiftMatrix s M)).ofLp j)) = 0 := by
  let Y : E n := nVec (shiftMatrix s M)
  have horth : inner ℝ Y (colVec (shiftMatrix s M) (emb k)) = 0 :=
    nVec_orthogonal_emb (shiftMatrix s M) k
  have hid : inner ℝ Y (colVec (shiftMatrix s M) (emb k))
      = ∑ j : Fin n, Y.ofLp j * (colVec (shiftMatrix s M) (emb k)).ofLp j := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Real.inner_apply]
  calc
    (∑ j : Fin n, (shiftMatrix s M) j (emb k) * ((nVec (shiftMatrix s M)).ofLp j))
        = ∑ j : Fin n, Y.ofLp j * (colVec (shiftMatrix s M) (emb k)).ofLp j := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [colVec_coeff]
            ring
    _ = inner ℝ Y (colVec (shiftMatrix s M) (emb k)) := hid.symm
    _ = 0 := horth

/-- Deterministic: `actSq` of the transposed first-`n−1` columns family on the
normal's coordinate function is zero. -/
lemma actSq_W_yfn_eq_zero {n : ℕ} (hn : 1 ≤ n) (M : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) :
    actSq (fun k : Fin (n - 1) => fun j : Fin n => (shiftMatrix s M) j (emb k))
          (fun j : Fin n => ((nVec (shiftMatrix s M)).ofLp j)) = 0 := by
  unfold actSq rowAct
  apply Finset.sum_eq_zero
  intro k hk
  have hz : (∑ j : Fin n, (shiftMatrix s M) j (emb k) * ((nVec (shiftMatrix s M)).ofLp j)) = 0 :=
    rowAct_W_yfn_eq_zero hn M s k
  have hpow := congrArg (fun z : ℝ => z ^ 2) hz
  simpa using hpow

/-- Deterministic: a `(δ,ν)`-compressible normal is a witness for the
compressible small-ball event of the shifted family (any `γ ≥ 0`). -/
lemma compressEvent_of_yfn_compressible {n : ℕ} (hn : 1 ≤ n)
    (M : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) {δ ν γ : ℝ} (hγ0 : 0 ≤ γ)
    (hcomp : Commons.LinearAlgebra.Net.compressible δ ν
      (fun j : Fin n => (nVec (shiftMatrix s M)).ofLp j)) :
    ∃ x : Fin n → ℝ, Commons.LinearAlgebra.Net.sqNorm x = 1 ∧
      Commons.LinearAlgebra.Net.compressible δ ν x ∧
      actSq (fun k : Fin (n - 1) => fun j : Fin n => (shiftMatrix s M) j (emb k)) x ≤
        γ ^ 2 * (n : ℝ) := by
  refine ⟨(fun j : Fin n => (nVec (shiftMatrix s M)).ofLp j), ?_, hcomp, ?_⟩
  · exact sqNorm_ofLp_of_unit (nVec_unit hn (shiftMatrix s M))
  · have hz : actSq (fun k : Fin (n - 1) => fun j : Fin n => (shiftMatrix s M) j (emb k))
        (fun j : Fin n => ((nVec (shiftMatrix s M)).ofLp j)) = 0 :=
      actSq_W_yfn_eq_zero hn M s
    rw [hz]
    have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    exact mul_nonneg (sq_nonneg γ) hn0

/-- Monotonicity of `(δ,ν)`-compressibility in the parameters. -/
lemma compressible_mono {n : ℕ} {δ δ' ν ν' : ℝ} (x : Fin n → ℝ)
    (hδ : δ ≤ δ') (hν : ν ≤ ν') (hν0 : 0 ≤ ν) :
    Commons.LinearAlgebra.Net.compressible δ ν x →
      Commons.LinearAlgebra.Net.compressible δ' ν' x := by
  intro hx
  rcases hx with ⟨hunit, z, hz, hcard⟩
  refine ⟨hunit, z, ?_, ?_⟩
  · have hsq : ν ^ 2 ≤ ν' ^ 2 := by
      exact sq_le_sq.mpr (by rw [abs_of_nonneg hν0, abs_of_nonneg (le_trans hν0 hν)]; exact hν)
    exact le_trans hz hsq
  · have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    exact le_trans hcard (mul_le_mul_of_nonneg_right hδ hn0)

/-- The coordinate function of the random unit normal of a shifted Bernoulli
matrix is `(δ,ν)`-compressible with probability at most `(1−p+ε)^n`; the
parameters come from Proposition l:compress (both `s+p ≠ 0` and centered
`p`-shift versions), law-only hypotheses. -/
theorem normal_compressible_le {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε : ℝ} (hε₀ : 0 < ε) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ ν : ℝ, 0 < ν ∧ ν < 1 ∧
      ∀ (n : ℕ) (h2n : 2 ≤ n), n₀ ≤ n → ∀ {Ω : Type u} [MeasurableSpace Ω]
        (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
        (B : Ω → Matrix (Fin n) (Fin n) ℝ)
        (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (B · x.1 x.2)) P)
        (hBlaw : ∀ i j : Fin n, HasLaw (B · i j) (bernoulliMeasure 1 0 p) P),
        ∀ s : ℝ,
          P.real {ω : Ω | Commons.LinearAlgebra.Net.compressible δ ν
            (fun j : Fin n => ((nVec (shiftMatrix s (B ω))).ofLp j))} ≤ (1 - (p : ℝ) + ε) ^ n := by
  classical
  rcases compress_theorem (p := p) hp₀ hp₁ hε₀ with ⟨n₀s, hn₀s2, hrest⟩
  rcases hrest with ⟨γs, hγs, hrest⟩
  rcases hrest with ⟨δs, hδs0, hδs1, hrest⟩
  rcases hrest with ⟨νs, hνs0, hνs1, hcps⟩
  rcases compress_theorem_centered (p := p) hp₀ hp₁ hε₀ with ⟨n₀c, hn₀c2, hrest⟩
  rcases hrest with ⟨γc, hγc, hrest⟩
  rcases hrest with ⟨δc, hδc0, hδc1, hrest⟩
  rcases hrest with ⟨νc, hνc0, hνc1, hcpc⟩
  let n₀ : ℕ := max n₀s n₀c
  let δ : ℝ := min δs δc
  let ν : ℝ := min νs νc
  have hn0ge : 2 ≤ n₀ := by
    dsimp [n₀]
    exact le_trans hn₀s2 (le_max_left n₀s n₀c)
  have hδpos : 0 < δ := by
    dsimp [δ]
    rcases le_total δs δc with h | h
    · rw [min_eq_left h]
      exact hδs0
    · rw [min_eq_right h]
      exact hδc0
  have hδlt : δ < 1 := by
    dsimp [δ]
    rcases le_total δs δc with h | h
    · rw [min_eq_left h]
      exact hδs1
    · rw [min_eq_right h]
      exact hδc1
  have hνpos : 0 < ν := by
    dsimp [ν]
    rcases le_total νs νc with h | h
    · rw [min_eq_left h]
      exact hνs0
    · rw [min_eq_right h]
      exact hνc0
  have hνlt : ν < 1 := by
    dsimp [ν]
    rcases le_total νs νc with h | h
    · rw [min_eq_left h]
      exact hνs1
    · rw [min_eq_right h]
      exact hνc1
  have hδsδ : δ ≤ δs := by
    dsimp [δ]
    exact min_le_left _ _
  have hδcδ : δ ≤ δc := by
    dsimp [δ]
    exact min_le_right _ _
  have hνsν : ν ≤ νs := by
    dsimp [ν]
    exact min_le_left _ _
  have hνcν : ν ≤ νc := by
    dsimp [ν]
    exact min_le_right _ _
  refine ⟨n₀, hn0ge, δ, hδpos, hδlt, ν, hνpos, hνlt, ?_⟩
  intro n h2n hn Ω _ms P _prob B hBind hBlaw s
  have h1n : 1 ≤ n := by omega
  rcases exists_measurable_clamped_matrix (P := P) B hBind hBlaw with
    ⟨Bc, hcm, hcind, hclaw, hcpt, hcae⟩
  let Bt : Fin (n - 1) → Fin n → Ω → ℝ := fun k j ω => Bc ω j (emb k)
  have hBtmeas : ∀ k j, Measurable (Bt k j) := by
    intro k j
    dsimp [Bt]
    exact hcm j (emb k)
  have hBtlaw : ∀ k j, HasLaw (Bt k j) (bernoulliMeasure 1 0 p) P := by
    intro k j
    dsimp [Bt]
    exact hclaw j (emb k)
  have hBtpt : ∀ k j ω, |Bt k j ω - (p : ℝ)| ≤ 1 := by
    intro k j ω
    dsimp [Bt]
    exact hcpt j (emb k) ω
  have hg : Function.Injective (fun kj : Fin (n - 1) × Fin n => (kj.2, emb kj.1)) := by
    intro a b h
    have h1 : a.2 = b.2 := congrArg Prod.fst h
    have h2 : emb a.1 = emb b.1 := congrArg Prod.snd h
    have h3 : a.1 = b.1 := emb_injective h2
    exact Prod.ext h3 h1
  have hBtind : iIndepFun (fun kj : Fin (n - 1) × Fin n => Bt kj.1 kj.2) P := by
    have hpre := ProbabilityTheory.iIndepFun.precomp
      (f := fun x : Fin n × Fin n => (Bc · x.1 x.2))
      (g := fun kj : Fin (n - 1) × Fin n => (kj.2, emb kj.1)) hg hcind
    dsimp [Bt]
    exact hpre
  let Yb : Set Ω := {ω : Ω | Commons.LinearAlgebra.Net.compressible δ ν
      (fun j : Fin n => ((nVec (shiftMatrix s (B ω))).ofLp j))}
  let Yc : Set Ω := {ω : Ω | Commons.LinearAlgebra.Net.compressible δ ν
      (fun j : Fin n => ((nVec (shiftMatrix s (Bc ω))).ofLp j))}
  let S : Set (Matrix (Fin n) (Fin n) ℝ) := {M : Matrix (Fin n) (Fin n) ℝ |
      Commons.LinearAlgebra.Net.compressible δ ν
        (fun j : Fin n => ((nVec (shiftMatrix s M)).ofLp j))}
  have hae' : ∀ i j : Fin n, (fun ω => B ω i j) =ᵐ[P] (fun ω => Bc ω i j) :=
    fun i j => (hcae i j).symm
  have htr := measureReal_matrix_event_eq_of_ae P B Bc hae' S
  have htrY : P.real Yb = P.real Yc := by
    have h1 : Yb = {ω : Ω | B ω ∈ S} := by
      ext ω
      simp [Yb, S]
    have h2 : Yc = {ω : Ω | Bc ω ∈ S} := by
      ext ω
      simp [Yc, S]
    rw [h1, h2]
    exact htr
  have hνnonneg : 0 ≤ ν := le_of_lt hνpos
  by_cases hs : s + (p : ℝ) ≠ 0
  · -- branch s + p ≠ 0: compress_theorem
    have hmain := hcps n (by omega : n₀s ≤ n) (Ω := Ω) P Bt hBtmeas hBtind hBtlaw hBtpt s hs
    let Es : Set Ω := {ω : Ω | ∃ x : Fin n → ℝ,
        Commons.LinearAlgebra.Net.compressible δs νs x ∧
        actSq (fun k : Fin (n - 1) => fun j : Fin n => Bt k j ω + s) x ≤ γs ^ 2 * (n : ℝ)}
    have hEs : P.real Es ≤ (1 - (p : ℝ) + ε) ^ n := by
      simpa [Es] using hmain
    have hYcEs : Yc ⊆ Es := by
      intro ω hω
      dsimp [Yc] at hω
      have hmono : Commons.LinearAlgebra.Net.compressible δs νs
          (fun j : Fin n => ((nVec (shiftMatrix s (Bc ω))).ofLp j)) :=
        compressible_mono (fun j : Fin n => ((nVec (shiftMatrix s (Bc ω))).ofLp j))
          hδsδ hνsν hνnonneg hω
      rcases compressEvent_of_yfn_compressible h1n (Bc ω) s hγs.le hmono with
        ⟨x, hx1, hxc, hxact⟩
      dsimp [Es]
      refine ⟨x, hxc, ?_⟩
      have hent : (fun k : Fin (n - 1) => fun j : Fin n => Bt k j ω + s) =
          (fun k : Fin (n - 1) => fun j : Fin n => (shiftMatrix s (Bc ω)) j (emb k)) := by
        funext k j
        dsimp [Bt]
        rw [shiftMatrix_apply]
      have heqAct : actSq (fun k : Fin (n - 1) => fun j : Fin n => Bt k j ω + s) x =
          actSq (fun k : Fin (n - 1) => fun j : Fin n => (shiftMatrix s (Bc ω)) j (emb k)) x :=
        congrArg (fun A : Fin (n - 1) → Fin n → ℝ => actSq A x) hent
      rwa [heqAct]
    calc
      P.real Yb = P.real Yc := htrY
      _ ≤ P.real Es := MeasureTheory.measureReal_mono hYcEs (measure_ne_top P Es)
      _ ≤ (1 - (p : ℝ) + ε) ^ n := hEs
  · -- branch s + p = 0: centered compress theorem
    have hs0 : s + (p : ℝ) = 0 := by
      by_contra hne
      exact hs hne
    have hmain := hcpc n (by omega : n₀c ≤ n) (Ω := Ω) P Bt hBtmeas hBtind hBtlaw hBtpt
    let Ec : Set Ω := {ω : Ω | ∃ x : Fin n → ℝ,
        Commons.LinearAlgebra.Net.compressible δc νc x ∧
        actSq (fun k : Fin (n - 1) => fun j : Fin n => Bt k j ω - (p : ℝ)) x ≤ γc ^ 2 * (n : ℝ)}
    have hEc : P.real Ec ≤ (1 - (p : ℝ) + ε) ^ n := by
      simpa [Ec] using hmain
    have hYcEc : Yc ⊆ Ec := by
      intro ω hω
      dsimp [Yc] at hω
      have hmono : Commons.LinearAlgebra.Net.compressible δc νc
          (fun j : Fin n => ((nVec (shiftMatrix s (Bc ω))).ofLp j)) :=
        compressible_mono (fun j : Fin n => ((nVec (shiftMatrix s (Bc ω))).ofLp j))
          hδcδ hνcν hνnonneg hω
      rcases compressEvent_of_yfn_compressible h1n (Bc ω) s hγc.le hmono with
        ⟨x, hx1, hxc, hxact⟩
      dsimp [Ec]
      refine ⟨x, hxc, ?_⟩
      have hent : (fun k : Fin (n - 1) => fun j : Fin n => Bt k j ω - (p : ℝ)) =
          (fun k : Fin (n - 1) => fun j : Fin n => (shiftMatrix s (Bc ω)) j (emb k)) := by
        funext k j
        dsimp [Bt]
        rw [shiftMatrix_apply]
        linarith
      have heqAct : actSq (fun k : Fin (n - 1) => fun j : Fin n => Bt k j ω - (p : ℝ)) x =
          actSq (fun k : Fin (n - 1) => fun j : Fin n => (shiftMatrix s (Bc ω)) j (emb k)) x :=
        congrArg (fun A : Fin (n - 1) → Fin n → ℝ => actSq A x) hent
      rwa [heqAct]
    calc
      P.real Yb = P.real Yc := htrY
      _ ≤ P.real Ec := MeasureTheory.measureReal_mono hYcEc (measure_ne_top P Ec)
      _ ≤ (1 - (p : ℝ) + ε) ^ n := hEc

end Submission.NormalCompress
