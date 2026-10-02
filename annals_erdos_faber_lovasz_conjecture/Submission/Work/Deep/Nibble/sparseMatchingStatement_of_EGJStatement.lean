import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.Defs
import Submission.Work.Deep.Nibble.thinning
import Submission.Work.Deep.Nibble.exists_threshold
import Submission.Work.Deep.Nibble.card_nat_le_of_degree_bound

/-!
# `cor:sparse_egj` from `thm:egj`

The file proves `SparseMatchingStatement` (Corollary `cor:sparse_egj` with the paper's
quantifier order, as defined in `Work.Deep.Nibble.Defs`) from `EGJStatement` (Theorem
`thm:egj` of Ehard–Glock–Joos, as recorded in `Submission/EFL/EGJ.lean`).

The proof is the paper's (efl.tex:503): apply `EGJStatement` to the subfamily
`{S ∈ 𝓕 : D^{1/20} ≤ |S|}` of the prescribed collection (with `Δ = (1+κ)D`), obtaining a
matching `M₀` covering a `(1 ± Δ^{-ε²})`-fraction of `degreeSum 𝓗 S / Δ` of every such `S`;
then *thin* `M₀`, keeping each of its edges independently with probability `1-γ`.  Since the
degrees of `𝓗` are `(1 ± κ)D`, the covered fraction `|S ∩ V(M₀)|/|S|` lies in
`[(1-κ)²/(1+κ), 1] ⊆ [(1-3κ), 1]`, so the shifted mean `(1-γ)|S ∩ V(M₀)|` is within
`3κ|S|` of `(1-γ)|S|`; the thinning deviation is `≤ 4κ|S|` by the weighted Chernoff bound
plus a union bound over the at most `n^{2 log n}` sets of `𝓕`.

For `κ ≥ 1/4` the empty matching already satisfies the conclusion, so only `κ < 1/4` is
non-trivial.

Everything is assembled here from the three delegated lemmas
`Work.Deep.Nibble.thinning` (the Chernoff + alteration step),
`Work.Deep.Nibble.exists_threshold` (the asymptotic side conditions) and
`Work.Deep.Nibble.card_nat_le_of_degree_bound` (the `|𝓗| ≤ nΔ` double count).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

/-- **Lower bound for the degree sum of a set.**  If every degree of `𝓗` is at least
`(1-κ)D` then `degreeSum 𝓗 S ≥ (1-κ)D·|S|`. -/
theorem degreeSum_ge_aux {n : ℕ} (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n))
    (S : Set (Fin n)) {D κ : ℝ}
    (hdeg : ∀ v : Fin n, |((hypergraphDegree 𝓗 v : ℝ)) - D| ≤ κ * D) :
    (1 - κ) * D * (S.ncard : ℝ) ≤ degreeSum 𝓗 S := by
  classical
  rw [degreeSum]
  have hset : ((Finset.univ.filter (fun v : Fin n => v ∈ S) : Finset (Fin n)) : Set (Fin n)) = S := by
    ext v; simp
  have hcard : ((Finset.univ.filter (fun v : Fin n => v ∈ S)).card : ℝ) = (S.ncard : ℝ) := by
    rw [← Set.ncard_coe_finset (s := (Finset.univ.filter (fun v : Fin n => v ∈ S))), hset]
  have h2 : ∀ v ∈ (Finset.univ.filter (fun v : Fin n => v ∈ S)),
      (1 - κ) * D ≤ ((hypergraphDegree 𝓗 v : ℝ)) := by
    intro v _
    have h := (abs_le.mp (hdeg v)).1
    linarith
  have h3 := Finset.card_nsmul_le_sum (Finset.univ.filter (fun v : Fin n => v ∈ S))
      (fun v => ((hypergraphDegree 𝓗 v : ℝ))) ((1 - κ) * D) h2
  rw [nsmul_eq_mul] at h3
  rw [hcard] at h3
  calc (1 - κ) * D * (S.ncard : ℝ) = (S.ncard : ℝ) * ((1 - κ) * D) := by ring
    _ ≤ _ := h3

/-- **Upper bound for the maximum degree.**  If every degree of `𝓗` is at most `(1+κ)D`
then `Δ(𝓗) ≤ (1+κ)D` (as a real number). -/
theorem maxDegree_cast_le_aux {n : ℕ} (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n))
    {D κ : ℝ} (hD : 0 ≤ D) (hκ : 0 ≤ κ)
    (hdeg : ∀ v : Fin n, |((hypergraphDegree 𝓗 v : ℝ)) - D| ≤ κ * D) :
    ((hypergraphMaxDegree 𝓗 : ℕ) : ℝ) ≤ (1 + κ) * D := by
  have hle : ∀ v : Fin n, hypergraphDegree 𝓗 v ≤ Nat.floor ((1 + κ) * D) := by
    intro v
    refine Nat.le_floor ?_
    have h := (abs_le.mp (hdeg v)).2
    linarith
  have hsup : hypergraphMaxDegree 𝓗 ≤ Nat.floor ((1 + κ) * D) := by
    rw [hypergraphMaxDegree]
    exact Finset.sup_le (fun v _ => hle v)
  calc ((hypergraphMaxDegree 𝓗 : ℕ) : ℝ)
      ≤ ((Nat.floor ((1 + κ) * D) : ℕ) : ℝ) := by exact_mod_cast hsup
    _ ≤ (1 + κ) * D := Nat.floor_le (by nlinarith)

/-- **The coverage estimate produced by `thm:egj`.**  If `|u - d/Δ| ≤ δ(d/Δ)`, `δ ≤ κ`,
`Δ = (1+κ)D`, `d ≥ (1-κ)D·s` and `s ≥ 0`, then `u ≥ (1-3κ)s`: this is
`(1-κ)²/(1+κ) ≥ 1-3κ` together with the EGJ error term `δ ≤ κ`. -/
theorem coverage_lower_aux {κ D Δ d u s δ : ℝ} (hκ0 : 0 < κ) (hκ : κ < 1 / 4) (hD : 0 < D)
    (hΔ : Δ = (1 + κ) * D) (hs : 0 ≤ s) (hds : (1 - κ) * D * s ≤ d)
    (hδ : δ ≤ κ) (hu : |u - d / Δ| ≤ δ * (d / Δ)) :
    (1 - 3 * κ) * s ≤ u := by
  have hΔpos : 0 < Δ := by rw [hΔ]; exact mul_pos (by linarith) hD
  have hdnn : 0 ≤ d := le_trans (mul_nonneg (mul_nonneg (by linarith) hD.le) hs) hds
  have h1 : (1 - δ) * (d / Δ) ≤ u := by
    have h := (abs_le.mp hu).1
    have : (1 - δ) * (d / Δ) = d / Δ - δ * (d / Δ) := by ring
    rw [this]; linarith
  have h2 : (1 - κ) * (d / Δ) ≤ (1 - δ) * (d / Δ) :=
    mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hdnn hΔpos.le)
  have h3 : (1 - κ) * ((1 - κ) * D * s / Δ) ≤ (1 - κ) * (d / Δ) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    exact div_le_div_of_nonneg_right hds hΔpos.le
  have h4 : (1 - κ) * ((1 - κ) * D * s / Δ) = (1 - κ) ^ 2 * s / (1 + κ) := by
    rw [hΔ]; field_simp
  have h5 : (1 - 3 * κ) * s ≤ (1 - κ) ^ 2 * s / (1 + κ) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 + κ)]
    nlinarith [hs, sq_nonneg κ]
  linarith

/-- **Corollary `cor:sparse_egj` from Theorem `thm:egj`, with the corrected
quantifier order.**

This differs from `ErdosFaberLovaszConjecture.SparseEGJStatement`
(`Submission/EFL/EGJ.lean:60`) only in that `∀ κ γ` now precedes `∃ n₀`, as in
the paper (`0 < 1/n₀ ≪ 1/r, κ, γ < 1`); see the note in
`Work.Deep.Nibble.Defs` for the parity counterexample showing that the seeded
order is false.  The proof is the paper's (efl.tex:503): apply `EGJStatement` to
the subfamily `{S ∈ 𝓕 : D^{1/20} ≤ |S|}` to get a matching `M₀` with
`|S ∩ V(M₀)| = (1 ± Δ^{-ε²})·degreeSum 𝓗 S/Δ`, then keep each edge of `M₀`
independently with probability `1-γ`.  Under the hypothesis that *all* degrees
of `𝓗` are `(1±κ)D`, this gives `|S ∖ V(M)| = (γ ± 4κ)|S|`, by Chernoff plus a
union bound over the at most `n^{2 log n}` sets of `𝓕`; the threshold `n₀` is
chosen large enough that `Δ₀(r) ≤ D`, `Δ^{-ε²} ≤ κ`, and the Chernoff–union
bound `2 log²n ≲ κ² D^{1/20}` hold.  For `κ ≥ 1/4` the empty matching already
satisfies the conclusion. -/
theorem sparseMatchingStatement_of_EGJStatement
    (h : ErdosFaberLovaszConjecture.EGJStatement) :
    ErdosFaberLovaszConjecture.SparseMatchingStatement := by
  classical
  intro r hr κ γ hκ0 hκ1 hγ0 hγ1
  by_cases hκbig : (1 : ℝ) / 4 ≤ κ
  · -- The empty matching works when `κ ≥ 1/4`.
    refine ⟨1, one_pos, fun n hn D hD 𝓗 hlin hunif hdeg 𝓕 h𝓕 => ?_⟩
    refine ⟨∅, isMatching_empty 𝓗, fun S hS hbig => ?_⟩
    have h1 : (S \ matchVert (∅ : Set 𝓗)).ncard = S.ncard := by
      simp [matchVert]
    rw [h1]
    have hs : (0 : ℝ) ≤ (S.ncard : ℝ) := Nat.cast_nonneg _
    have hγ : (0 : ℝ) ≤ 1 - γ := by linarith
    rw [show ((S.ncard : ℝ) - γ * (S.ncard : ℝ)) = (1 - γ) * (S.ncard : ℝ) by ring]
    rw [abs_of_nonneg (mul_nonneg hγ hs)]
    nlinarith [hs, hκbig, hγ]
  · push Not at hκbig
    obtain ⟨Δ₀, hΔ₀pos, hEGJ⟩ := h r hr
    obtain ⟨n₀, hn₀pos, hn₀⟩ := exists_threshold hr hκ0 hκbig hΔ₀pos
    refine ⟨n₀, hn₀pos, fun n hn D hD 𝓗 hlin hunif hdeg 𝓕 h𝓕 => ?_⟩
    obtain ⟨hD1, hc1, hc2, hc3, hc4, hc5, hc6⟩ := hn₀ n hn D hD
    set Δ : ℝ := (1 + κ) * D with hΔdef
    set 𝓕₀ : Set (Set (Fin n)) := {S | S ∈ 𝓕 ∧ D ^ ((1 : ℝ) / 20) ≤ (S.ncard : ℝ)} with h𝓕₀def
    -- ## The three hypotheses of `EGJStatement` at `Δ = (1+κ)D`
    have hcard𝓗 : (Nat.card 𝓗 : ℝ) ≤ Real.exp (Δ ^ ((1 / (1500 * (r : ℝ) ^ 2)) ^ 2)) := by
      have h1 : (Nat.card 𝓗 : ℝ) ≤ (n : ℝ) * ((1 + κ) * D) := by
        refine card_nat_le_of_degree_bound (n := n) (𝓗 := 𝓗) (r := r) (D := (1 + κ) * D)
          (by omega) hunif (fun v => ?_)
        have hv := (abs_le.mp (hdeg v)).2
        linarith
      have h2 : (n : ℝ) * ((1 + κ) * D) ≤ 2 * (n : ℝ) * D := by
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
        have hD0 : (0 : ℝ) ≤ D := by linarith
        have hk1 : (1 + κ) ≤ 2 := by linarith
        nlinarith
      have h3 : 2 * (n : ℝ) * D ≤
          Real.exp (((1 + κ) * D) ^ ((1 / (1500 * (r : ℝ) ^ 2)) ^ 2)) := hc3
      rw [hΔdef]
      exact le_trans (le_trans h1 h2) h3
    have hcard𝓕₀ : (𝓕₀.ncard : ℝ) ≤ Real.exp (Δ ^ ((1 / (1500 * (r : ℝ) ^ 2)) ^ 2)) := by
      have h1 : 𝓕₀.ncard ≤ 𝓕.ncard := Set.ncard_mono (fun S hS => hS.1)
      have h2 : (𝓕₀.ncard : ℝ) ≤ (n : ℝ) ^ (2 * Real.log n) :=
        le_trans (by exact_mod_cast h1) h𝓕
      rw [hΔdef]
      exact le_trans h2 hc4
    have hmaxdeg : ((hypergraphMaxDegree 𝓗 : ℕ) : ℝ) ≤ Δ := by
      rw [hΔdef]
      exact maxDegree_cast_le_aux 𝓗 (by linarith) hκ0.le hdeg
    have hdegSum : ∀ S ∈ 𝓕₀, Δ ^ ((26 : ℝ) / 25) ≤ degreeSum 𝓗 S := by
      intro S hS
      have hbig : D ^ ((1 : ℝ) / 20) ≤ (S.ncard : ℝ) := hS.2
      have hlow := degreeSum_ge_aux 𝓗 S hdeg
      have hD0 : (0 : ℝ) < D := by linarith
      have hκ1 : (0 : ℝ) < 1 - κ := by linarith
      have hstep1 : (1 - κ) * D * D ^ ((1 : ℝ) / 20) ≤ (1 - κ) * D * (S.ncard : ℝ) :=
        mul_le_mul_of_nonneg_left hbig (mul_nonneg (le_of_lt hκ1) (le_of_lt hD0))
      have hstep2 : D * D ^ ((1 : ℝ) / 20) = D ^ ((21 : ℝ) / 20) := by
        have hpow : D ^ ((21 : ℝ) / 20) = D ^ ((1 : ℝ) + (1 : ℝ) / 20) := by norm_num
        rw [hpow, Real.rpow_add (by linarith : (0 : ℝ) < D), Real.rpow_one]
      have hstep3 : ((1 + κ) * D) ^ ((26 : ℝ) / 25) ≤ (1 - κ) * D ^ ((21 : ℝ) / 20) := hc5
      calc Δ ^ ((26 : ℝ) / 25) = ((1 + κ) * D) ^ ((26 : ℝ) / 25) := by rw [hΔdef]
        _ ≤ (1 - κ) * D ^ ((21 : ℝ) / 20) := hstep3
        _ = (1 - κ) * D * D ^ ((1 : ℝ) / 20) := by rw [← hstep2]; ring
        _ ≤ (1 - κ) * D * (S.ncard : ℝ) := hstep1
        _ ≤ degreeSum 𝓗 S := hlow
    -- ## Apply `thm:egj`
    obtain ⟨M₀, hM₀match, hM₀cov⟩ :=
      hEGJ Δ hc1 n 𝓗 hlin hunif hmaxdeg hcard𝓗 𝓕₀ hcard𝓕₀ hdegSum
    -- ## The coverage hypothesis of the thinning lemma
    have hlower : ∀ S ∈ 𝓕₀,
        (1 - 3 * κ) * (S.ncard : ℝ) ≤ ((S ∩ matchVert M₀).ncard : ℝ) := by
      intro S hS
      have hcov := hM₀cov S hS
      have hlow := degreeSum_ge_aux 𝓗 S hdeg
      have hδ : Δ ^ (-((1 / (1500 * (r : ℝ) ^ 2)) ^ 2)) ≤ κ := by rw [hΔdef]; exact hc2
      exact coverage_lower_aux hκ0 hκbig (by linarith) hΔdef (Nat.cast_nonneg _) hlow hδ hcov
    -- ## The union bound
    have hcard𝓕₀le : (Fintype.card ↥𝓕₀ : ℝ) ≤ (n : ℝ) ^ (2 * Real.log n) := by
      have h1 : Fintype.card ↥𝓕₀ = 𝓕₀.ncard := by
        rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      rw [h1]
      have hsub : 𝓕₀ ⊆ 𝓕 := fun S hS => hS.1
      have hmono : 𝓕₀.ncard ≤ 𝓕.ncard := Set.ncard_mono hsub
      exact le_trans (by exact_mod_cast hmono) h𝓕
    have hunion : 2 * (Fintype.card ↥𝓕₀ : ℝ) *
        Real.exp (-(3 / 8 * κ ^ 2 * D ^ ((1 : ℝ) / 20) / r)) < 1 := by
      have h2 : (Fintype.card ↥𝓕₀ : ℝ) * 2 ≤ (n : ℝ) ^ (2 * Real.log n) * 2 :=
        mul_le_mul_of_nonneg_right hcard𝓕₀le (by norm_num)
      have hE : (0 : ℝ) ≤ Real.exp (-(3 / 8 * κ ^ 2 * D ^ ((1 : ℝ) / 20) / r)) := Real.exp_nonneg _
      have h3 : 2 * (Fintype.card ↥𝓕₀ : ℝ) *
          Real.exp (-(3 / 8 * κ ^ 2 * D ^ ((1 : ℝ) / 20) / r)) ≤
          2 * (n : ℝ) ^ (2 * Real.log n) *
            Real.exp (-(3 / 8 * κ ^ 2 * D ^ ((1 : ℝ) / 20) / r)) := by nlinarith
      exact lt_of_le_of_lt h3 hc6
    -- ## Thin the matching
    have hthin : ∃ M : Set 𝓗, M ⊆ M₀ ∧ IsMatching 𝓗 M ∧
        ∀ a : 𝓕₀, |((((a : Set (Fin n))) \ matchVert M).ncard : ℝ)
          - γ * (((a : Set (Fin n))).ncard : ℝ)| ≤
            4 * κ * (((a : Set (Fin n))).ncard : ℝ) := by
      exact thinning (n := n) (𝓗 := 𝓗) (M₀ := M₀) (σ := 𝓕₀)
        (S := fun a => (a : Set (Fin n))) (r := (r : ℝ))
        (hM₀ := hM₀match) (hκ0 := hκ0) (hκ := hκbig) (hγ0 := le_of_lt hγ0)
        (hγ1 := hγ1) (hr := by exact_mod_cast (show 0 < r by omega)) (hD1 := hD1)
        (hsize := fun e _ => by rw [hunif (e : Set (Fin n)) e.2])
        (hbig := fun a => a.2.2) (hlower := fun a => hlower a.1 a.2) (hunion := hunion)
    obtain ⟨M, _hMsub, hMmatch, hMprop⟩ := hthin
    exact ⟨M, hMmatch, fun S hS hbig => hMprop ⟨S, hS, hbig⟩⟩

end Work.Deep.Nibble
