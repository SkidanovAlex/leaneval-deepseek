import Mathlib
import Submission.Work.LT.Defs

namespace Work.LT

open Finset

/-! ## Auxiliary lemmas for the DELLM Lemma 4.4 slice bound -/

/-- Fibre splitting of the Hamming weight over the first coordinate. -/
lemma hammingNorm_prod_fst {G : Type} [Fintype G] {Δ : ℕ} (w : G × Fin Δ → ZMod 2) :
    hammingNorm w = ∑ g : G, hammingNorm (fun j : Fin Δ => w (g, j)) := by
  rw [show hammingNorm w = Fintype.card {p : G × Fin Δ // w p ≠ 0} from by
        rw [hammingNorm]; exact (Fintype.card_subtype _).symm]
  rw [show (∑ g : G, hammingNorm (fun j : Fin Δ => w (g, j)))
        = ∑ g : G, Fintype.card {j : Fin Δ // w (g, j) ≠ 0} from by
        congr 1 with g
        rw [hammingNorm]; exact (Fintype.card_subtype _).symm]
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr
    (Equiv.subtypeProdEquivSigmaSubtype (fun (g : G) (j : Fin Δ) => w (g, j) ≠ 0))

/-- Fibre splitting of the Hamming weight over the "head" coordinate
`h ↦ Σ_j #{w (h * (B j)⁻¹, j) ≠ 0}`. -/
lemma hammingNorm_prod_snd {G : Type} [Group G] [Fintype G] {Δ : ℕ} (B : Fin Δ → G)
    (w : G × Fin Δ → ZMod 2) :
    hammingNorm w = ∑ h : G, hammingNorm (fun j : Fin Δ => w (h * (B j)⁻¹, j)) := by
  let w' : G × Fin Δ → ZMod 2 := fun p => w (p.1 * (B p.2)⁻¹, p.2)
  have hcard : hammingNorm w = hammingNorm w' := by
    rw [show hammingNorm w = Fintype.card {p : G × Fin Δ // w p ≠ 0} from by
          rw [hammingNorm]; exact (Fintype.card_subtype _).symm,
        show hammingNorm w' = Fintype.card {p : G × Fin Δ // w' p ≠ 0} from by
          rw [hammingNorm]; exact (Fintype.card_subtype _).symm]
    refine Fintype.card_congr ?_
    refine
      { toFun := fun p => ⟨(p.1.1 * B p.1.2, p.1.2), ?_⟩
        invFun := fun q => ⟨(q.1.1 * (B q.1.2)⁻¹, q.1.2), q.2⟩
        left_inv := ?_
        right_inv := ?_ }
    · show w' (p.1.1 * B p.1.2, p.1.2) ≠ 0
      dsimp only [w']
      rw [show (p.1.1 * B p.1.2) * (B p.1.2)⁻¹ = p.1.1 by
            rw [mul_assoc, mul_inv_cancel, mul_one]]
      exact p.2
    · intro p; obtain ⟨⟨g, j⟩, hp⟩ := p
      simp [mul_assoc]
    · intro q; obtain ⟨⟨g, j⟩, hq⟩ := q
      simp [mul_assoc]
  rw [hcard, hammingNorm_prod_fst w']

/-- `√(s t) ≤ max s t` for `s, t ≥ 0`. -/
lemma sqrt_mul_le_max {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Real.sqrt (s * t) ≤ max s t := by
  rcases le_total s t with h | h
  · rw [max_eq_right h]
    calc Real.sqrt (s * t) ≤ Real.sqrt (t * t) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right h ht)
      _ = t := Real.sqrt_mul_self ht
  · rw [max_eq_left h]
    calc Real.sqrt (s * t) ≤ Real.sqrt (s * s) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h hs)
      _ = s := Real.sqrt_mul_self hs

/-- The real-arithmetic heart of the slice bound. -/
private lemma slice_arith {δ0 μ d R N hwR : ℝ} (hμ : 0 ≤ μ) (hδ : μ ≤ δ0) (hd : 0 < d)
    (hR : 0 < R) (hN : 0 < N)
    (hlow : δ0 * d * R ≤ hwR) (hupN : hwR * N ≤ d * R * R + μ * d * R * N) :
    δ0 * (δ0 - μ) * (N * d) ≤ hwR := by
  have h1 : δ0 * d * R * N ≤ hwR * N :=
    mul_le_mul_of_nonneg_right hlow (le_of_lt hN)
  have h2 : (δ0 - μ) * (d * R * N) ≤ d * R * R := by nlinarith [h1, hupN]
  have h2b : (d * R) * ((δ0 - μ) * N) ≤ (d * R) * R := by nlinarith [h2]
  have h2' : (δ0 - μ) * N ≤ R := (mul_le_mul_iff_of_pos_left (mul_pos hd hR)).mp h2b
  have hδ0nn : 0 ≤ δ0 := le_trans hμ hδ
  have h3 : δ0 * d * ((δ0 - μ) * N) ≤ δ0 * d * R := by
    have hc : 0 ≤ δ0 * d := mul_nonneg hδ0nn (le_of_lt hd)
    nlinarith [mul_le_mul_of_nonneg_left h2' hc]
  have h4 : δ0 * (δ0 - μ) * (N * d) = δ0 * d * ((δ0 - μ) * N) := by ring
  linarith

/-- **Bipartite expander mixing for the right walk of `B`** (DELLM, mixing step of Lemma 4.4).
The number of edges with tail in `S` and head in `T` is at most
`Δ |S| |T| / |G| + μ Δ √(|S| |T|)`. -/
theorem lr_mix {G : Type} [Group G] [Fintype G] [DecidableEq G] {Δ : ℕ} (B : Fin Δ → G)
    (μ : ℝ) (hμ : 0 ≤ μ) (hΔ : 0 < Δ) (hB : rightExpander B μ) (S T : Finset G) :
    (∑ g ∈ S, ((Finset.univ.filter (fun j : Fin Δ => g * B j ∈ T)).card : ℝ))
      ≤ (Δ : ℝ) * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card G : ℝ)
        + μ * (Δ : ℝ) * Real.sqrt ((S.card : ℝ) * (T.card : ℝ)) := by
  classical
  set N : ℝ := (Fintype.card G : ℝ) with hN
  set d : ℝ := (Δ : ℝ) with hd
  set f : G → ℝ := (fun h => if h ∈ T then 1 else 0) with hf
  set m : ℝ := (T.card : ℝ) / N with hm
  set y : G → ℝ := (fun h => f h - m) with hy
  set z : G → ℝ := (fun g => (∑ j : Fin Δ, y (g * B j)) / d) with hz
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  have hdpos : 0 < d := by rw [hd]; exact_mod_cast hΔ
  -- data about `f`
  have hf_sum : ∑ h : G, f h = (T.card : ℝ) := by
    rw [hf, Finset.sum_boole]; simp
  have hf_mean : ∑ h : G, f h = N * m := by
    rw [hf_sum, hm]; field_simp
  have hf_sq : ∑ h : G, f h ^ 2 = (T.card : ℝ) := by
    rw [show ∑ h : G, f h ^ 2 = ∑ h : G, f h from by
      refine Finset.sum_congr rfl (fun h _ => ?_)
      rw [hf]; simp only []
      by_cases hh : h ∈ T
      · rw [ite_eq_left hh]; norm_num
      · rw [ite_eq_right hh]; norm_num]
    exact hf_sum
  -- mean-zero function `y`
  have hy_sum : ∑ h : G, y h = 0 := by
    rw [hy, Finset.sum_sub_distrib, hf_mean]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN]
    ring
  -- variance of `y`
  have hy_sq : ∑ h : G, y h ^ 2 = ∑ h : G, f h ^ 2 - N * m ^ 2 := by
    rw [hy]
    have h1 : ∀ h, (f h - m) ^ 2 = f h ^ 2 - 2 * m * f h + m ^ 2 := fun h => by ring
    simp_rw [h1]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [show (∑ h : G, 2 * m * f h) = 2 * m * ∑ h : G, f h by rw [Finset.mul_sum]]
    rw [show (∑ _h : G, m ^ 2) = N * m ^ 2 by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN]]
    rw [hf_mean]; ring
  have hY_le : ∑ h : G, y h ^ 2 ≤ (T.card : ℝ) := by
    rw [hy_sq, hf_sq]
    have : 0 ≤ N * m ^ 2 := mul_nonneg (le_of_lt hNpos) (sq_nonneg m)
    linarith
  -- expander hypothesis applied to `y`
  have hBapp : ∑ g : G, z g ^ 2 ≤ μ ^ 2 * ∑ g : G, y g ^ 2 := by
    have h := hB y hy_sum
    rw [hz, hd]
    exact (le_of_eq (Finset.sum_congr rfl (fun g _ => rfl))).trans h
  have hZsq_le : (∑ g ∈ S, z g ^ 2) ≤ μ ^ 2 * ∑ g : G, y g ^ 2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun i _ _ => sq_nonneg (z i))).trans hBapp
  -- Cauchy–Schwarz
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt S z (fun _ => (1 : ℝ))
  have hcard1 : (∑ _g ∈ S, (1 : ℝ) ^ 2) = (S.card : ℝ) := by
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [hcard1] at hcs
  rw [show (∑ g ∈ S, z g * 1) = ∑ g ∈ S, z g by simp] at hcs
  have hZ_bound : (∑ g ∈ S, z g) ≤ μ * Real.sqrt (T.card : ℝ) * Real.sqrt (S.card : ℝ) := by
    refine hcs.trans ?_
    have h1 : Real.sqrt (∑ g ∈ S, z g ^ 2) ≤ μ * Real.sqrt (T.card : ℝ) := by
      refine (Real.sqrt_le_sqrt hZsq_le).trans ?_
      rw [Real.sqrt_mul (sq_nonneg μ), Real.sqrt_sq hμ]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hY_le) hμ
    exact mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
  -- the two cardinal expressions agree
  have hE1 : (∑ g ∈ S, ((Finset.univ.filter (fun j : Fin Δ => g * B j ∈ T)).card : ℝ))
      = ∑ g ∈ S, ∑ j : Fin Δ, f (g * B j) := by
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [Finset.sum_boole]
  have hE2 : (∑ g ∈ S, ∑ j : Fin Δ, f (g * B j))
      = d * (∑ g ∈ S, z g) + d * (S.card : ℝ) * m := by
    have h1 : ∀ g, (∑ j : Fin Δ, f (g * B j)) = (∑ j : Fin Δ, y (g * B j)) + d * m := by
      intro g
      rw [show ∑ j : Fin Δ, f (g * B j) = ∑ j : Fin Δ, (y (g * B j) + m) from by
            refine Finset.sum_congr rfl (fun j _ => ?_); rw [hy]; ring]
      rw [Finset.sum_add_distrib]
      rw [show (∑ _j : Fin Δ, m) = d * m by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hd]]
    simp_rw [h1, Finset.sum_add_distrib]
    rw [show (∑ g ∈ S, ∑ j : Fin Δ, y (g * B j)) = d * ∑ g ∈ S, z g from by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun g _ => ?_)
          rw [hz, mul_div_cancel₀ _ (ne_of_gt hdpos)]]
    rw [show (∑ g ∈ S, d * m) = d * (S.card : ℝ) * m from by
          rw [Finset.sum_const, nsmul_eq_mul]; ring]
  -- putting it together
  refine (hE1.trans hE2).trans_le ?_
  have hstep : d * (∑ g ∈ S, z g) ≤ d * (μ * Real.sqrt (T.card : ℝ) * Real.sqrt (S.card : ℝ)) :=
    mul_le_mul_of_nonneg_left hZ_bound (le_of_lt hdpos)
  have hsqrt : Real.sqrt ((S.card : ℝ) * (T.card : ℝ)) = Real.sqrt (S.card : ℝ) * Real.sqrt (T.card : ℝ) :=
    Real.sqrt_mul (by exact_mod_cast Nat.zero_le S.card) _
  rw [hsqrt, hm, mul_div_assoc]
  nlinarith [hstep]

/-- **One slice of DELLM Lemma 4.4.** Let `w : G × Fin Δ → 𝔽₂` be a Tanner codeword on the
bipartite graph with edges `g — g * B j` (`B` may repeat): every row `j ↦ w (g, j)` and every
"anti-row" `j ↦ w (h * (B j)⁻¹, j)` lies in `CB`. Then, if the right walk of `B` is a `μ`-expander
and nonzero words of `CB` have weight `≥ δ0 Δ`, the support of `w` has at least `δ0 (δ0 - μ) |G| Δ`
edges. (Hypotheses `0 ≤ μ ≤ δ0` make `δ0 ≥ 0`; `0 < Δ` and `w ≠ 0` make the two vertex sets
nonempty.)

Route: `S = {g : row g ≠ 0}`, `T = {h : anti-row h ≠ 0}`; each `g ∈ S` and each `h ∈ T` carries
`≥ δ0 Δ` support edges, so `|supp w| ≥ δ0 Δ max(|S|,|T|) ≥ δ0 Δ √(|S||T|)`; also
`|supp w| ≤ Σ_{g∈S} #{j : g * B j ∈ T}`; and bipartite mixing, i.e.
`Σ_{g∈S} #{j : g * B j ∈ T} ≤ Δ|S||T|/|G| + μ Δ √(|S||T|)` proved from `hB` (split `1_T` into its
mean plus a mean-zero part, apply `hB`, Cauchy–Schwarz), bounds `|supp w|` from above; combine and
divide by `Δ √(|S||T|) > 0`.

NOTE for the prover: a colleague is proving exactly the mixing step as
`Work.LT.lr_mixing` in `Submission/Work/LT/lr_mixing.lean` (statement: for `S T : Finset G`,
`(S.sum fun g => (Finset.univ.filter (fun j => g * B j ∈ T)).card : ℝ) ≤ Δ * S.card * T.card / |G| + μ * Δ * Real.sqrt (S.card * T.card)`, under `0 ≤ μ` and `rightExpander B μ`). If that file
exists when you start, import it and apply it; if not, prove the mixing bound inline in your own
file (do not block on it). -/
theorem lr_slice_bound {G : Type} [Group G] [Fintype G] {Δ : ℕ} (B : Fin Δ → G)
    (CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)) (δ0 μ : ℝ) (hμ : 0 ≤ μ) (hδ0 : μ ≤ δ0)
    (hB : rightExpander B μ)
    (hdB : ∀ x ∈ CB, x ≠ 0 → δ0 * Δ ≤ hammingNorm x)
    (w : G × Fin Δ → ZMod 2)
    (hrow : ∀ g : G, (fun j : Fin Δ => w (g, j)) ∈ CB)
    (hcol : ∀ h : G, (fun j : Fin Δ => w (h * (B j)⁻¹, j)) ∈ CB)
    (hw : w ≠ 0) (hΔ : 0 < Δ) :
    δ0 * (δ0 - μ) * ((Fintype.card G : ℝ) * (Δ : ℝ)) ≤ (hammingNorm w : ℝ) := by
  classical
  set S : Finset G := Finset.univ.filter (fun g => (fun j : Fin Δ => w (g, j)) ≠ 0) with hS
  set T : Finset G := Finset.univ.filter (fun h => (fun j : Fin Δ => w (h * (B j)⁻¹, j)) ≠ 0) with hT
  -- the two vertex sets are nonempty
  obtain ⟨p, hp⟩ : ∃ p : G × Fin Δ, w p ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hw (funext h)
  obtain ⟨g₀, j₀⟩ := p
  have hg₀ : g₀ ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun hz => hp (by simpa using congrFun hz j₀)⟩
  have hh₀ : g₀ * B j₀ ∈ T := by
    rw [hT, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun hz => hp ?_⟩
    have := congrFun hz j₀
    simpa [mul_assoc, mul_inv_cancel, mul_one] using this
  have hSpos : 0 < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨g₀, hg₀⟩
  have hTpos : 0 < (T.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨_, hh₀⟩
  -- notations for the numeric quantities
  set N : ℝ := (Fintype.card G : ℝ) with hN
  set d : ℝ := (Δ : ℝ) with hd
  set s : ℝ := (S.card : ℝ) with hs
  set t : ℝ := (T.card : ℝ) with ht
  set R : ℝ := Real.sqrt (s * t) with hR
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  have hdpos : 0 < d := by rw [hd]; exact_mod_cast hΔ
  have hspos : 0 < s := by rw [hs]; exact hSpos
  have htpos : 0 < t := by rw [ht]; exact hTpos
  have hRpos : 0 < R := by
    rw [hR]; exact Real.sqrt_pos.mpr (mul_pos hspos htpos)
  have hR2 : R * R = s * t := by
    rw [hR, ← pow_two]
    exact Real.sq_sqrt (le_of_lt (mul_pos hspos htpos))
  -- splitting the Hamming weight
  have hsplitS : (hammingNorm w : ℝ)
      = ∑ g : G, (hammingNorm (fun j : Fin Δ => w (g, j)) : ℝ) := by
    rw [hammingNorm_prod_fst]; push_cast; rfl
  have hsplitT : (hammingNorm w : ℝ)
      = ∑ h : G, (hammingNorm (fun j : Fin Δ => w (h * (B j)⁻¹, j)) : ℝ) := by
    rw [hammingNorm_prod_snd B]; push_cast; rfl
  -- lower bound from `S`
  have hlowS : δ0 * d * s ≤ (hammingNorm w : ℝ) := by
    rw [hsplitS]
    calc δ0 * d * s = ∑ _g ∈ S, (δ0 * d) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ g ∈ S, (hammingNorm (fun j : Fin Δ => w (g, j)) : ℝ) := by
            refine Finset.sum_le_sum (fun g hg => ?_)
            have hne : (fun j : Fin Δ => w (g, j)) ≠ 0 := by
              rw [hS] at hg; exact (Finset.mem_filter.mp hg).2
            exact hdB (fun j : Fin Δ => w (g, j)) (hrow g) hne
      _ ≤ ∑ g : G, (hammingNorm (fun j : Fin Δ => w (g, j)) : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
              (fun i _ _ => Nat.cast_nonneg _)
  -- lower bound from `T`
  have hlowT : δ0 * d * t ≤ (hammingNorm w : ℝ) := by
    rw [hsplitT]
    calc δ0 * d * t = ∑ _h ∈ T, (δ0 * d) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ h ∈ T, (hammingNorm (fun j : Fin Δ => w (h * (B j)⁻¹, j)) : ℝ) := by
            refine Finset.sum_le_sum (fun h hh => ?_)
            have hne : (fun j : Fin Δ => w (h * (B j)⁻¹, j)) ≠ 0 := by
              rw [hT] at hh; exact (Finset.mem_filter.mp hh).2
            exact hdB (fun j : Fin Δ => w (h * (B j)⁻¹, j)) (hcol h) hne
      _ ≤ ∑ h : G, (hammingNorm (fun j : Fin Δ => w (h * (B j)⁻¹, j)) : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
              (fun i _ _ => Nat.cast_nonneg _)
  -- combine into the lower bound involving `R`
  have hlow : δ0 * d * R ≤ (hammingNorm w : ℝ) := by
    have hδ0d : 0 ≤ δ0 * d := mul_nonneg (le_trans hμ hδ0) (le_of_lt hdpos)
    have hRle : R ≤ max s t := by
      rw [hR]; exact sqrt_mul_le_max (le_of_lt hspos) (le_of_lt htpos)
    have hmax : δ0 * d * max s t ≤ (hammingNorm w : ℝ) := by
      rcases le_total s t with h | h
      · rw [max_eq_right h]; exact hlowT
      · rw [max_eq_left h]; exact hlowS
    exact (mul_le_mul_of_nonneg_left hRle hδ0d).trans hmax
  -- upper bound from `S`
  have hterm_card : ∀ g ∈ S, (hammingNorm (fun j : Fin Δ => w (g, j)) : ℝ)
      ≤ ((Finset.univ.filter (fun j : Fin Δ => g * B j ∈ T)).card : ℝ) := by
    intro g _
    have hsub2 : (Finset.univ.filter (fun j : Fin Δ => w (g, j) ≠ 0))
        ⊆ (Finset.univ.filter (fun j : Fin Δ => g * B j ∈ T)) := by
      intro j hj
      rw [Finset.mem_filter] at hj ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hT, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun hz => hj.2 ?_⟩
      have := congrFun hz j
      simpa [mul_assoc, mul_inv_cancel, mul_one] using this
    have := Finset.card_le_card hsub2
    rw [hammingNorm]
    exact_mod_cast this
  have hup : (hammingNorm w : ℝ)
      ≤ ∑ g ∈ S, ((Finset.univ.filter (fun j : Fin Δ => g * B j ∈ T)).card : ℝ) := by
    rw [hsplitS]
    have hzero : ∀ g ∉ S, (hammingNorm (fun j : Fin Δ => w (g, j)) : ℝ) = 0 := by
      intro g hg
      have hrow0 : (fun j : Fin Δ => w (g, j)) = 0 := by
        rw [hS, Finset.mem_filter] at hg
        simpa only [Finset.mem_univ, true_and, not_not] using hg
      rw [hrow0, hammingNorm_zero]; norm_num
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun x _ hx => hzero x hx)]
    exact Finset.sum_le_sum hterm_card
  -- the mixing bound
  have hmix : (∑ g ∈ S, ((Finset.univ.filter (fun j : Fin Δ => g * B j ∈ T)).card : ℝ))
      ≤ d * s * t / N + μ * d * R := by
    have h := lr_mix B μ hμ hΔ hB S T
    rw [← hd, ← hs, ← ht, ← hN, ← hR] at h
    exact h
  have hupN : (hammingNorm w : ℝ) * N ≤ d * R * R + μ * d * R * N := by
    have h1 : (hammingNorm w : ℝ) ≤ d * s * t / N + μ * d * R := hup.trans hmix
    have hmul : (d * s * t / N + μ * d * R) * N = d * s * t + μ * d * R * N := by
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hNpos)]
    have hdt : d * s * t = d * R * R := by rw [mul_assoc, ← hR2, mul_assoc]
    have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hNpos)
    rw [hmul, hdt] at h2
    exact h2
  -- final arithmetic
  exact slice_arith hμ hδ0 hdpos hRpos hNpos hlow hupN

end Work.LT
