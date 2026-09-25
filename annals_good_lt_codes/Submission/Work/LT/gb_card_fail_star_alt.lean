import Mathlib
import Submission.Work.LT.good_base_defs
import Submission.Work.LT.gb_card_submodule
import Submission.Work.LT.gb_card_subspaces
import Submission.Work.LT.gb_card_preimage_submodule
import Submission.Work.LT.gb_submodule_le_equiv
import Submission.Work.LT.gb_wt_helpers
import Submission.Work.LT.gb_basic
import Submission.Work.LT.gb_card_submodule_sharp
import Submission.Work.LT.gb_card_ker_contains
import Submission.Work.LT.gb_card_sparse_submodule
import Submission.Work.LT.gb_exists_submodule_finrank
import Submission.Work.LT.gb_star_numeric_sum

namespace Work.LT

open scoped BigOperators

/-! ## Elementary `rpow` manipulations with base `2` -/

lemma gbAlt_rpow2_mul (a b : ℝ) : (2:ℝ)^a * (2:ℝ)^b = (2:ℝ)^(a+b) :=
  (Real.rpow_add (by norm_num) a b).symm

lemma gbAlt_rpow2_split (a b : ℝ) : (2:ℝ)^(a+b) = (2:ℝ)^a * (2:ℝ)^b :=
  Real.rpow_add (by norm_num) a b

lemma gbAlt_rpow2_pow (a : ℝ) (n : ℕ) : ((2:ℝ)^a)^n = (2:ℝ)^(a*(n:ℝ)) := by
  rw [← Real.rpow_natCast ((2:ℝ)^a) n]
  exact (Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) a (n:ℝ)).symm

lemma gbAlt_rpow2_nat (n : ℕ) : (2:ℝ)^n = (2:ℝ)^(n:ℝ) := (Real.rpow_natCast 2 n).symm

/-! ## The two counting types used in the union bound -/

/-- The "bad" parity-check matrices: those whose kernel code fails property `(*)`. -/
abbrev gbAltBad (D r : ℕ) (α : ℝ) : Type :=
  {H : Fin r → Fin D → ZMod 2 // ¬ GB.HasStar α r (GB.kerCode H)}

/-- Pairs `(V, H)` of an `α`-sparse `m`-dimensional `V` and a matrix `H` whose kernel code
meets `V` in dimension at least `m/2`. -/
abbrev gbAltSm (D r : ℕ) (α : ℝ) (m : ℕ) : Type :=
  Σ (V : {V : Submodule (ZMod 2) (Fin D → ZMod 2) // GB.IsSparse α V ∧ GB.frk V = m}),
    {H : Fin r → Fin D → ZMod 2 // 2 * GB.frk (GB.kerCode H ⊓ V.1) ≥ m}

/-- Triples `(V, W, H)`: `V ≤ 𝔽₂^D` `α`-sparse of dimension `m`, `W ≤ V` of dimension `⌈m/2⌉`,
and `H` a parity-check matrix whose kernel contains `W`. -/
abbrev gbAltTm (D r : ℕ) (α : ℝ) (m : ℕ) : Type :=
  Σ (V : {V : Submodule (ZMod 2) (Fin D → ZMod 2) // GB.IsSparse α V ∧ GB.frk V = m}),
    Σ (W : {W : Submodule (ZMod 2) (Fin D → ZMod 2) // W ≤ V.1 ∧ GB.frk W = (m+1)/2}),
      {H : Fin r → Fin D → ZMod 2 // W.1 ≤ GB.kerCode H}

/-- **Union bound over `V` and `W`.**  The number of `H` for which there is an `α`-sparse
`m`-dimensional `V` with `dim(ker H ⊓ V) ≥ m/2` is at most the number of `H` containing some
`⌈m/2⌉`-dimensional `W ≤ V` in the kernel. -/
theorem gbAlt_sm_le_tm (D r : ℕ) (α : ℝ) (m : ℕ) :
    Nat.card (gbAltSm D r α m) ≤ Nat.card (gbAltTm D r α m) := by
  classical
  apply Nat.card_le_card_of_surjective
    (f := fun p => (⟨p.1, ⟨p.2.2.1, by
       have hle : p.2.1.1 ≤ GB.kerCode p.2.2.1 ⊓ p.1.1 := le_inf p.2.2.2 p.2.1.2.1
       have hfrk : GB.frk (GB.kerCode p.2.2.1 ⊓ p.1.1) ≥ GB.frk p.2.1.1 :=
         Submodule.finrank_mono hle
       rw [p.2.1.2.2] at hfrk
       omega⟩⟩))
  intro H
  have h2 : 2 * GB.frk (GB.kerCode H.2.1 ⊓ H.1.1) ≥ m := H.2.2
  have hk : (m + 1)/2 ≤ GB.frk (GB.kerCode H.2.1 ⊓ H.1.1) := by omega
  obtain ⟨W, hWV, hWfrk⟩ :=
    gb_exists_submodule_finrank (GB.kerCode H.2.1 ⊓ H.1.1) ((m+1)/2) hk
  exact ⟨⟨H.1, ⟨W, hWV.trans inf_le_right, hWfrk⟩, ⟨H.2.1, hWV.trans inf_le_left⟩⟩, rfl⟩

/-- **Counting bound for a fixed dimension `m`.**  With `s = |smallVecs α D|`,
`#{H : ∃ α-sparse m-dimensional V, dim(ker H ⊓ V) ≥ m/2}`
`≤ s^m · 4 · 2^{⌈m/2⌉(m-⌈m/2⌉)} · 2^{r(D-⌈m/2⌉)}`. -/
theorem gbAlt_sm_bound (D r : ℕ) (α : ℝ) (m : ℕ) :
    (Nat.card (gbAltSm D r α m) : ℝ)
      ≤ ((GB.smallVecs α D).card : ℝ)^m * 4 * (2:ℝ)^(((m+1)/2)*(m - (m+1)/2))
          * (2:ℝ)^((r:ℝ)*((D:ℝ) - (((m+1)/2:ℕ):ℝ))) := by
  classical
  refine (Nat.cast_le.mpr (gbAlt_sm_le_tm D r α m)).trans ?_
  have hTm : (Nat.card (gbAltTm D r α m) : ℝ)
      = ∑ V : {V : Submodule (ZMod 2) (Fin D → ZMod 2) // GB.IsSparse α V ∧ GB.frk V = m},
          (Nat.card {W : Submodule (ZMod 2) (Fin D → ZMod 2) // W ≤ V.1 ∧ GB.frk W = (m+1)/2} : ℝ)
            * (2:ℝ)^((r:ℝ)*((D:ℝ) - (((m+1)/2:ℕ):ℝ))) := by
    rw [Nat.card_sigma, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun V _ => ?_)
    rw [Nat.card_sigma, Nat.cast_sum]
    rw [Finset.sum_congr rfl (fun W _ => by rw [gb_card_ker_contains, W.2.2])]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  rw [hTm]
  have hle : ∑ V : {V : Submodule (ZMod 2) (Fin D → ZMod 2) // GB.IsSparse α V ∧ GB.frk V = m},
        (Nat.card {W : Submodule (ZMod 2) (Fin D → ZMod 2) // W ≤ V.1 ∧ GB.frk W = (m+1)/2} : ℝ)
          * (2:ℝ)^((r:ℝ)*((D:ℝ) - (((m+1)/2:ℕ):ℝ)))
      ≤ ∑ _V : {V : Submodule (ZMod 2) (Fin D → ZMod 2) // GB.IsSparse α V ∧ GB.frk V = m},
          (4 * (2:ℝ)^(((m+1)/2)*(m - (m+1)/2))) * (2:ℝ)^((r:ℝ)*((D:ℝ) - (((m+1)/2:ℕ):ℝ))) := by
    apply Finset.sum_le_sum
    intro V _
    have hs := gb_card_submodule_sharp V.1 ((m+1)/2)
    rw [V.2.2] at hs
    exact mul_le_mul_of_nonneg_right hs (by positivity)
  refine hle.trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  have hsp : (Nat.card {V : Submodule (ZMod 2) (Fin D → ZMod 2) // GB.IsSparse α V ∧ GB.frk V = m} : ℝ)
      ≤ ((GB.smallVecs α D).card : ℝ)^m := gb_card_sparse_submodule α m
  refine (mul_le_mul_of_nonneg_right hsp (by positivity)).trans (le_of_eq ?_)
  ring

/-- **Combining the factors into a single power.**  For `0 ≤ s ≤ 2^{βD}`,
`s^m · 4 · 2^{⌈m/2⌉(m-⌈m/2⌉)} · 2^{r(D-⌈m/2⌉)} ≤ 2^{rD} · 2^{βDm + 2 + ⌈m/2⌉(m-⌈m/2⌉) - r⌈m/2⌉}`. -/
lemma gbAlt_term_le {D r m : ℕ} {β s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ (2:ℝ)^(β*(D:ℝ))) :
    s^m * 4 * (2:ℝ)^(((m+1)/2)*(m - (m+1)/2)) * (2:ℝ)^((r:ℝ)*((D:ℝ) - (((m+1)/2:ℕ):ℝ)))
    ≤ (2:ℝ)^((r:ℝ)*(D:ℝ)) * (2:ℝ)^(β*(D:ℝ)*(m:ℝ) + (((m+1)/2:ℕ):ℝ)*(((m - (m+1)/2 : ℕ)):ℝ) + 2 - (r:ℝ)*(((m+1)/2:ℕ):ℝ)) := by
  have hsA : s^m ≤ (2:ℝ)^(β*(D:ℝ)*(m:ℝ)) := by
    calc s^m ≤ ((2:ℝ)^(β*(D:ℝ)))^m := pow_le_pow_left₀ hs0 hs m
      _ = (2:ℝ)^(β*(D:ℝ)*(m:ℝ)) := gbAlt_rpow2_pow _ _
  have h4 : (4:ℝ) = (2:ℝ)^(2:ℝ) := by norm_num
  have hB : (2:ℝ)^(((m+1)/2)*(m - (m+1)/2))
      = (2:ℝ)^((((m+1)/2:ℕ):ℝ)*(((m - (m+1)/2 : ℕ)):ℝ)) := by
    rw [gbAlt_rpow2_nat]; congr 1; push_cast; ring
  rw [h4, hB]
  calc s^m * (2:ℝ)^(2:ℝ) * (2:ℝ)^((((m+1)/2:ℕ):ℝ)*(((m - (m+1)/2 : ℕ)):ℝ))
          * (2:ℝ)^((r:ℝ)*((D:ℝ) - (((m+1)/2:ℕ):ℝ)))
      ≤ (2:ℝ)^(β*(D:ℝ)*(m:ℝ)) * (2:ℝ)^(2:ℝ) * (2:ℝ)^((((m+1)/2:ℕ):ℝ)*(((m - (m+1)/2 : ℕ)):ℝ))
          * (2:ℝ)^((r:ℝ)*((D:ℝ) - (((m+1)/2:ℕ):ℝ))) := by
        gcongr
    _ = (2:ℝ)^(β*(D:ℝ)*(m:ℝ) + 2 + (((m+1)/2:ℕ):ℝ)*(((m - (m+1)/2 : ℕ)):ℝ)
            + ((r:ℝ)*((D:ℝ) - (((m+1)/2:ℕ):ℝ)))) := by
        rw [gbAlt_rpow2_mul (β*(D:ℝ)*(m:ℝ)) 2,
            gbAlt_rpow2_mul (β*(D:ℝ)*(m:ℝ) + 2) ((((m+1)/2:ℕ):ℝ)*(((m - (m+1)/2 : ℕ)):ℝ)),
            gbAlt_rpow2_mul (β*(D:ℝ)*(m:ℝ) + 2 + ((((m+1)/2:ℕ):ℝ)*(((m - (m+1)/2 : ℕ)):ℝ)))
              ((r:ℝ)*((D:ℝ) - (((m+1)/2:ℕ):ℝ)))]
    _ = (2:ℝ)^((r:ℝ)*(D:ℝ)) * (2:ℝ)^(β*(D:ℝ)*(m:ℝ) + (((m+1)/2:ℕ):ℝ)*(((m - (m+1)/2 : ℕ)):ℝ) + 2 - (r:ℝ)*(((m+1)/2:ℕ):ℝ)) := by
        rw [← gbAlt_rpow2_split ((r:ℝ)*(D:ℝ))
              (β*(D:ℝ)*(m:ℝ) + (((m+1)/2:ℕ):ℝ)*(((m - (m+1)/2 : ℕ)):ℝ) + 2 - (r:ℝ)*(((m+1)/2:ℕ):ℝ))]
        congr 1
        ring

/-- Kalachev--Panteleev Lemma 5 in the "kernel of a random parity-check matrix" model (alternative proof; the statement is identical to `Work.LT.gb_card_fail_star`). Proof plan: for each `m ≤ r` and each `α`-sparse `V` of dimension `m`, the `H` with `dim(ker H ⊓ V) ≥ m/2` are those for which some `k = ⌈m/2⌉`-dimensional `W ≤ V` satisfies `W ≤ ker H`; `#{H : W ≤ ker H} = 2^{r(D-k)}`; the number of `k`-dimensional `W ≤ V` is at most `4 * 2^{k(m-k)}` (Gaussian binomial, `GB.gb_card_subspaces`); the number of `α`-sparse `m`-dimensional `V` is at most `|smallVecs α D|^m ≤ 2^{βDm}`; summing `2^{βDm - k(r-m+k)}` over `m ≤ r` using `8βD + 4 ≤ r` gives `2^{rD - r/8}`.  Useful existing lemmas: `GB.gb_card_subspaces`, `GB.gb_card_preimage_submodule`, `GB.gb_submodule_le_equiv`, and `card_filter_eq_natCard` / `card_fun_zmod_cast` from `Submission.Work.LT.gb_basic`. -/
theorem gb_card_fail_star_alt {D r : ℕ} (α β : ℝ) (hα : 0 < α) (hr : 8 * β * D + 4 ≤ r)
    (hS : (Nat.card {v : Fin D → ZMod 2 // (hammingNorm v : ℝ) ≤ α * D} : ℝ) ≤
      (2 : ℝ) ^ (β * D)) :
    (Nat.card {H : Fin r → Fin D → ZMod 2 // ¬ GB.HasStar α r (GB.kerCode H)} : ℝ) ≤
      (2 : ℝ) ^ (r * D) * (2 : ℝ) ^ (-(r : ℝ) / 8) := by
  classical
  -- `hS` in terms of `smallVecs`
  have hScard : ((GB.smallVecs α D).card : ℝ)
      = (Nat.card {v : Fin D → ZMod 2 // (hammingNorm v : ℝ) ≤ α * D} : ℝ) := by
    rw [GB.smallVecs, card_filter_eq_natCard]
  have hS' : ((GB.smallVecs α D).card : ℝ) ≤ (2:ℝ)^(β*D) := by rw [hScard]; exact hS
  have h0mem : (0 : Fin D → ZMod 2) ∈ GB.smallVecs α D := by
    rw [GB.mem_smallVecs]
    simp only [hammingNorm]
    simp
    positivity
  have hcard1 : (1:ℕ) ≤ (GB.smallVecs α D).card := Finset.card_pos.mpr ⟨0, h0mem⟩
  -- `0 ≤ β D`
  have hβ0 : 0 ≤ β*D := by
    have h2 : (2:ℝ)^(0:ℝ) ≤ (2:ℝ)^(β*D) := by
      have h1 : ((1:ℕ):ℝ) ≤ ((GB.smallVecs α D).card : ℝ) := by exact_mod_cast hcard1
      rw [Real.rpow_zero]
      simpa using h1.trans hS'
    exact (rpow_two_le_iff).mp h2
  -- hence `4 ≤ r`
  have h4r : 4 ≤ r := by
    have h4R : (4:ℝ) ≤ (r:ℝ) := by nlinarith [hr, hβ0]
    exact_mod_cast h4R
  rcases lt_or_eq_of_le h4r with h5 | h4eq
  · -- the main case `5 ≤ r`
    have h5' : 5 ≤ r := h5
    -- union bound: `|Bad| ≤ ∑_m |gbAltSm m|`
    have hstep : (Nat.card (gbAltBad D r α) : ℝ) ≤
        ∑ m ∈ (Finset.Icc 1 r : Finset ℕ), (Nat.card (gbAltSm D r α m) : ℝ) := by
      let f : (Σ m : {m : ℕ // m ∈ Finset.Icc 1 r}, gbAltSm D r α m.1) → gbAltBad D r α :=
        fun p => ⟨p.2.2.1, by
          intro hstar
          have h := hstar p.2.1.1 p.2.1.2.1
            (by rw [p.2.1.2.2]; exact (Finset.mem_Icc.mp p.1.2).1)
            (by rw [p.2.1.2.2]; exact (Finset.mem_Icc.mp p.1.2).2)
          have h2 := p.2.2.2
          rw [p.2.1.2.2] at h
          omega⟩
      have hsurj : Function.Surjective f := by
        intro H
        have hH := H.2
        simp only [GB.HasStar] at hH
        push Not at hH
        obtain ⟨V, hsp, hpos, hle_r, hcond⟩ := hH
        have hk : (GB.frk V + 1) / 2 ≤ GB.frk (GB.kerCode H.1 ⊓ V) := by omega
        obtain ⟨W, hWV, hWfrk⟩ :=
          gb_exists_submodule_finrank (GB.kerCode H.1 ⊓ V) ((GB.frk V + 1)/2) hk
        exact ⟨⟨⟨GB.frk V, Finset.mem_Icc.mpr ⟨hpos, hle_r⟩⟩,
          ⟨⟨V, hsp, rfl⟩, ⟨H.1, by omega⟩⟩⟩, Subtype.ext rfl⟩
      have h1 : Nat.card (gbAltBad D r α) ≤
          Nat.card (Σ m : {m : ℕ // m ∈ Finset.Icc 1 r}, gbAltSm D r α m.1) :=
        Nat.card_le_card_of_surjective f hsurj
      refine (Nat.cast_le.mpr h1).trans_eq ?_
      rw [Nat.card_sigma, Nat.cast_sum, Finset.univ_eq_attach (Finset.Icc 1 r),
          Finset.sum_attach (Finset.Icc 1 r) (fun n : ℕ => (Nat.card (gbAltSm D r α n) : ℝ))]
    -- per-`m` bound
    have hperM : ∀ m ∈ (Finset.Icc 1 r : Finset ℕ),
        (Nat.card (gbAltSm D r α m) : ℝ)
          ≤ (2:ℝ)^((r:ℝ)*(D:ℝ))
            * (2:ℝ)^(β*(D:ℝ)*(m:ℝ) + (((m+1)/2:ℕ):ℝ)*(((m - (m+1)/2 : ℕ)):ℝ) + 2
                - (r:ℝ)*(((m+1)/2:ℕ):ℝ)) := by
      intro m _
      exact (gbAlt_sm_bound D r α m).trans (gbAlt_term_le (by positivity) hS')
    have hnum := gb_star_numeric_sum h5' (v := β*(D:ℝ)) (by linarith [hβ0]) (by nlinarith [hr])
    have hsum : (∑ m ∈ (Finset.Icc 1 r : Finset ℕ), (Nat.card (gbAltSm D r α m) : ℝ))
        ≤ (2:ℝ)^((r:ℝ)*(D:ℝ)) * (2:ℝ)^(-(r:ℝ)/8) := by
      calc (∑ m ∈ (Finset.Icc 1 r : Finset ℕ), (Nat.card (gbAltSm D r α m) : ℝ))
          ≤ ∑ m ∈ (Finset.Icc 1 r : Finset ℕ), (2:ℝ)^((r:ℝ)*(D:ℝ))
              * (2:ℝ)^(β*(D:ℝ)*(m:ℝ) + (((m+1)/2:ℕ):ℝ)*(((m - (m+1)/2 : ℕ)):ℝ) + 2
                  - (r:ℝ)*(((m+1)/2:ℕ):ℝ)) :=
            Finset.sum_le_sum hperM
        _ = (2:ℝ)^((r:ℝ)*(D:ℝ))
              * ∑ m ∈ (Finset.Icc 1 r : Finset ℕ), (2:ℝ)^(β*(D:ℝ)*(m:ℝ)
                  + (((m+1)/2:ℕ):ℝ)*(((m - (m+1)/2 : ℕ)):ℝ) + 2 - (r:ℝ)*(((m+1)/2:ℕ):ℝ)) := by
            rw [Finset.mul_sum]
        _ ≤ (2:ℝ)^((r:ℝ)*(D:ℝ)) * (2:ℝ)^(-(r:ℝ)/8) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            refine le_of_eq_of_le ?_ hnum
            apply Finset.sum_congr rfl
            intro m _
            congr 1
            ring
    calc (Nat.card (gbAltBad D r α) : ℝ)
        ≤ (2:ℝ)^((r:ℝ)*(D:ℝ)) * (2:ℝ)^(-(r:ℝ)/8) := hstep.trans hsum
      _ = (2:ℝ)^(r*D) * (2:ℝ)^(-(r:ℝ)/8) := by rw [rpow_two_mul_nat]
  · -- the degenerate case `r = 4`
    have hβD0 : β * (D:ℝ) = 0 := by
      have hr4 : (8:ℝ)*β*(D:ℝ) + 4 ≤ 4 := by rw [← h4eq] at hr; exact hr
      nlinarith [hr4, hβ0]
    have hcard_le : ((GB.smallVecs α D).card : ℝ) ≤ 1 := by
      have hh := hS'
      rw [hβD0] at hh
      simpa using hh
    have hcard_eq : (GB.smallVecs α D).card = 1 := by
      have hle : (GB.smallVecs α D).card ≤ 1 := by exact_mod_cast hcard_le
      omega
    -- the only small vector is `0`; hence the only sparse subspace is `⊥`
    have hsv : GB.smallVecs α D = {0} := by
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard_eq
      have ha0 : a = 0 := by
        have h0' : (0 : Fin D → ZMod 2) ∈ ({a} : Finset (Fin D → ZMod 2)) := by
          rw [← ha]; exact h0mem
        rw [Finset.mem_singleton] at h0'
        exact h0'.symm
      rw [ha, ha0]
    have hfrk0 : ∀ V : Submodule (ZMod 2) (Fin D → ZMod 2), GB.IsSparse α V → GB.frk V = 0 := by
      intro V hsp
      obtain ⟨S, hSS, hspan⟩ := hsp
      have hS0 : ∀ v ∈ S, v = 0 := by
        intro v hv
        have : v ∈ GB.smallVecs α D := by rw [GB.mem_smallVecs]; exact hSS v hv
        rw [hsv, Finset.mem_singleton] at this
        exact this
      have hV : V = ⊥ := by
        rw [← hspan]
        exact le_antisymm
          (Submodule.span_le.mpr (fun v hv => by rw [hS0 v hv]; exact Submodule.zero_mem _)) bot_le
      rw [hV]
      simp [GB.frk]
    have hEmpty : IsEmpty (gbAltBad D r α) :=
      ⟨fun H => H.2 (fun V hsp hpos _ => by
        rw [hfrk0 V hsp] at hpos; exact absurd hpos (lt_irrefl 0))⟩
    have hz : Nat.card (gbAltBad D r α) = 0 := Nat.card_eq_zero.mpr (Or.inl hEmpty)
    rw [hz, Nat.cast_zero]
    positivity

end Work.LT
