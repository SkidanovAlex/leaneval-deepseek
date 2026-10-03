import Mathlib
import Submission.Work.FIArea7CF.card_pairs_gBox_absDelta_lt
import Submission.Work.FIArea4.A4c.Defs

namespace Work.FIArea4.A4c

/-- **The pair count of the junk cut** (design `Submission/Work/FIArea4/AREA4_ENGINES_LEAD.md` §3.3, node N7): the number of ordered pairs `(z₁,z₂)` of the box `gBox (radN Pa)` with `|Δ(z₁,z₂)| ≤ 4X²` is `≤ 100000·X²·N^{3/2}`.

This is the crude triple count of the junk cut: `junkCut X m` with `1 ≤ m < X` forces `d ≤ X`,
`m < d` and `|Δ(z₁,z₂)| ≤ 4dm < 4X²`, so every contributing pair has `|Δ| ≤ 4X²`.

Route (either of the following suffices; `Pa.N ≥ 1`, `R := radN Pa`):
* `Work.FIArea7.card_pairs_gBox_absDelta_lt` (its constant is `C = 40`) at `M := 4X² + 1` (so that
  `|Δ| ≤ 4X² ↔ |Δ| < M`) gives `# ≤ 40·(4X²+2)·(((2R+1).toNat) : ℝ)² + 40·(((2R+1).toNat) : ℝ)³`;
  with `((R).toNat : ℝ) ≤ 4√N` (`Work.FIArea4.radN_toNat_le`) one has `((2R+1).toNat : ℝ) ≤ 9√N`
  and hence `# ≤ 40·(4X²+2)·81N + 40·729N^{3/2} ≤ 48600·X²N^{3/2}` since `X ≥ 1`, `N ≥ 1`;
* or the sharp per-`z₂` fibre count `Work.FIArea7.card_z1_absDelta_le` (from the same file) summed
  over the Chebyshev shells of `gBox R`.

Either way the constant `100000` has ample room. -/
theorem card_pairs_junk_le (Pa : Work.FITop.Params) (X : ℕ) (hX : 1 ≤ X) :
    ((((Work.FIPlan.gBox (Work.FITop.radN Pa)).product
        (Work.FIPlan.gBox (Work.FITop.radN Pa))).filter
        (fun p : GaussianInt × GaussianInt => Work.FIPlan.absDelta p.1 p.2 ≤ 4 * X * X)).card : ℝ)
      ≤ 100000 * (X : ℝ) ^ 2 * Pa.N ^ ((3 : ℝ) / 2) := by
  set R : ℤ := Work.FITop.radN Pa with hRdef
  set M : ℕ := 4 * X * X + 1 with hMdef
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hNnn : (0 : ℝ) ≤ Pa.N := by linarith
  have hNpos : (0 : ℝ) < Pa.N := by linarith
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hX2 : (1 : ℝ) ≤ (X : ℝ) ^ 2 := by nlinarith [sq_nonneg ((X : ℝ) - 1), hX1]
  have hRnn : (0 : ℤ) ≤ R := by
    rw [hRdef, Work.FITop.radN]
    exact Int.natCast_nonneg _
  have hsq1 : (1 : ℝ) ≤ Real.sqrt Pa.N := Real.one_le_sqrt.mpr hN1
  -- ### the Chebyshev radius of the box
  have hRle9 : (((2 * R + 1).toNat : ℝ)) ≤ 9 * Real.sqrt Pa.N := by
    have htoNat : (2 * R + 1).toNat = 2 * R.toNat + 1 := by
      have hRcast : R = ((R.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hRnn).symm
      have h2 : 2 * R + 1 = (((2 * R.toNat + 1 : ℕ)) : ℤ) := by
        conv_lhs => rw [hRcast]
        push_cast
        ring
      rw [h2, Int.toNat_natCast]
    rw [htoNat]
    push_cast
    have hRtoNat : ((R.toNat : ℕ) : ℝ) ≤ 4 * Real.sqrt Pa.N := by
      rw [hRdef]
      exact Work.FIArea4.radN_toNat_le Pa
    linarith
  -- ### reduction of the filter to a strict inequality
  have hfilter : ((Work.FIPlan.gBox R).product (Work.FIPlan.gBox R)).filter
        (fun p : GaussianInt × GaussianInt => Work.FIPlan.absDelta p.1 p.2 ≤ 4 * X * X)
      = ((Work.FIPlan.gBox R).product (Work.FIPlan.gBox R)).filter
        (fun p : GaussianInt × GaussianInt => Work.FIPlan.absDelta p.1 p.2 < M) := by
    refine Finset.filter_congr (fun p _ => ?_)
    rw [hMdef]
    exact Nat.lt_succ_iff.symm
  rw [hfilter]
  -- ### decomposition into the fibres over `z₂`
  have hdecompN : (((Work.FIPlan.gBox R).product (Work.FIPlan.gBox R)).filter
        (fun p : GaussianInt × GaussianInt => Work.FIPlan.absDelta p.1 p.2 < M)).card
      = ∑ z2 ∈ Work.FIPlan.gBox R,
          ((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card := by
    rw [show (Work.FIPlan.gBox R).product (Work.FIPlan.gBox R)
        = Work.FIPlan.gBox R ×ˢ Work.FIPlan.gBox R from rfl]
    rw [Finset.card_filter, Finset.sum_product, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun z2 _ => ?_)
    rw [Finset.card_filter]
  have hdecomp : ((((Work.FIPlan.gBox R).product (Work.FIPlan.gBox R)).filter
        (fun p : GaussianInt × GaussianInt => Work.FIPlan.absDelta p.1 p.2 < M)).card : ℝ)
      = ∑ z2 ∈ Work.FIPlan.gBox R,
          (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card : ℝ) := by
    rw [hdecompN, Nat.cast_sum]
  have h0mem : (0 : GaussianInt) ∈ Work.FIPlan.gBox R := by
    rw [Work.FIArea7.mem_gBox_iff_gRadius hRnn]
    simp [Work.FIArea7.gRadius]
  have hsplit : ∑ z2 ∈ Work.FIPlan.gBox R,
        (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card : ℝ)
      = (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 0 < M)).card : ℝ)
        + ∑ z2 ∈ (Work.FIPlan.gBox R).erase 0,
            (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card : ℝ) := by
    have hs := Finset.sum_erase_add (Work.FIPlan.gBox R)
      (fun z2 => (((Work.FIPlan.gBox R).filter
        (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card : ℝ)) h0mem
    rw [add_comm] at hs
    exact hs.symm
  -- ### the two fibre bounds
  have hboxcard : ((Work.FIPlan.gBox R).card : ℝ) = (((2 * R + 1).toNat : ℝ)) ^ 2 := by
    rw [Work.FIArea7.card_gBox_eq]
    push_cast
    ring
  have hC0 : (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 0 < M)).card : ℝ)
      ≤ (((2 * R + 1).toNat : ℝ)) ^ 2 := by
    have hle : ((Work.FIPlan.gBox R).filter
        (fun z1 => Work.FIPlan.absDelta z1 0 < M)).card ≤ (Work.FIPlan.gBox R).card :=
      Finset.card_filter_le _ _
    calc (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 0 < M)).card : ℝ)
        ≤ ((Work.FIPlan.gBox R).card : ℝ) := by exact_mod_cast hle
      _ = (((2 * R + 1).toNat : ℝ)) ^ 2 := hboxcard
  have hCne : ∀ z2 ∈ (Work.FIPlan.gBox R).erase 0,
      (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card : ℝ)
        ≤ ((2 * R + 1).toNat : ℝ) * (2 * (M : ℝ) + 1) := by
    intro z2 hz2
    rw [Finset.mem_erase] at hz2
    have h : ((Work.FIPlan.gBox R).filter
        (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card
        ≤ (2 * R + 1).toNat * (2 * M / Work.FIArea7.gRadius z2 + 1) :=
      Work.FIArea7.card_z1_absDelta_le R M z2 hz2.1
    have hnat : ((Work.FIPlan.gBox R).filter
        (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card
        ≤ (2 * R + 1).toNat * (2 * M + 1) :=
      h.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.div_le_self _ _) 1))
    calc (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card : ℝ)
        ≤ (((2 * R + 1).toNat * (2 * M + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = ((2 * R + 1).toNat : ℝ) * (2 * (M : ℝ) + 1) := by push_cast; ring
  have herasecard : (((Work.FIPlan.gBox R).erase 0).card : ℝ) ≤ (((2 * R + 1).toNat : ℝ)) ^ 2 := by
    have hle : ((Work.FIPlan.gBox R).erase 0).card ≤ (Work.FIPlan.gBox R).card :=
      Finset.card_le_card (Finset.erase_subset _ _)
    calc (((Work.FIPlan.gBox R).erase 0).card : ℝ) ≤ ((Work.FIPlan.gBox R).card : ℝ) := by
          exact_mod_cast hle
      _ = (((2 * R + 1).toNat : ℝ)) ^ 2 := hboxcard
  -- ### assembly of the crude count
  have htotal : ((((Work.FIPlan.gBox R).product (Work.FIPlan.gBox R)).filter
        (fun p : GaussianInt × GaussianInt => Work.FIPlan.absDelta p.1 p.2 < M)).card : ℝ)
      ≤ ((2 * R + 1).toNat : ℝ) ^ 2
        * (1 + ((2 * R + 1).toNat : ℝ) * (2 * (M : ℝ) + 1)) := by
    have hsum' : ∑ z2 ∈ (Work.FIPlan.gBox R).erase 0,
        (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card : ℝ)
        ≤ ((2 * R + 1).toNat : ℝ) ^ 2
          * (((2 * R + 1).toNat : ℝ) * (2 * (M : ℝ) + 1)) := by
      calc ∑ z2 ∈ (Work.FIPlan.gBox R).erase 0,
              (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card : ℝ)
          ≤ ∑ _z2 ∈ (Work.FIPlan.gBox R).erase 0,
              ((2 * R + 1).toNat : ℝ) * (2 * (M : ℝ) + 1) := Finset.sum_le_sum hCne
        _ = ((2 * R + 1).toNat : ℝ) * (2 * (M : ℝ) + 1)
              * (((Work.FIPlan.gBox R).erase 0).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            ring_nf
        _ ≤ ((2 * R + 1).toNat : ℝ) * (2 * (M : ℝ) + 1) * (((2 * R + 1).toNat : ℝ)) ^ 2 :=
            mul_le_mul_of_nonneg_left herasecard (by positivity)
        _ = ((2 * R + 1).toNat : ℝ) ^ 2
              * (((2 * R + 1).toNat : ℝ) * (2 * (M : ℝ) + 1)) := by ring
    rw [hdecomp, hsplit]
    linarith [hC0, hsum']
  -- ### the final arithmetic
  have hN32eq : Pa.N ^ ((3 : ℝ) / 2) = Pa.N * Real.sqrt Pa.N := by
    have h3 : ((3 : ℝ) / 2) = 1 + 1 / 2 := by norm_num
    rw [h3, Real.rpow_add hNpos, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hN32nn : (0 : ℝ) ≤ Pa.N ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hNnn _
  have hN32ge : Pa.N ≤ Pa.N ^ ((3 : ℝ) / 2) := by
    rw [hN32eq]
    nlinarith [hNnn, Real.sqrt_nonneg Pa.N, hsq1]
  have hsqrt3 : (Real.sqrt Pa.N) ^ 3 = Pa.N ^ ((3 : ℝ) / 2) := by
    have h1 : (Real.sqrt Pa.N) ^ 3 = (Real.sqrt Pa.N) ^ 2 * Real.sqrt Pa.N := by ring
    rw [h1, Real.sq_sqrt hNnn]
    exact hN32eq.symm
  have hRz2 : (((2 * R + 1).toNat : ℝ)) ^ 2 ≤ 81 * Pa.N := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (((2 * R + 1).toNat : ℝ))) hRle9 2
    have hs : (Real.sqrt Pa.N) ^ 2 = Pa.N := Real.sq_sqrt hNnn
    nlinarith [h, hs, Real.sqrt_nonneg Pa.N]
  have hRz3 : (((2 * R + 1).toNat : ℝ)) ^ 3 ≤ 729 * Pa.N ^ ((3 : ℝ) / 2) := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (((2 * R + 1).toNat : ℝ))) hRle9 3
    calc (((2 * R + 1).toNat : ℝ)) ^ 3 ≤ (9 * Real.sqrt Pa.N) ^ 3 := h
      _ = 729 * (Real.sqrt Pa.N) ^ 3 := by ring
      _ = 729 * Pa.N ^ ((3 : ℝ) / 2) := by rw [hsqrt3]
  have hM2 : 2 * (M : ℝ) + 1 ≤ 11 * (X : ℝ) ^ 2 := by
    rw [hMdef]; push_cast; nlinarith [hX2]
  have hNle : Pa.N ≤ (X : ℝ) ^ 2 * Pa.N ^ ((3 : ℝ) / 2) := by
    calc Pa.N ≤ Pa.N ^ ((3 : ℝ) / 2) := hN32ge
      _ = 1 * Pa.N ^ ((3 : ℝ) / 2) := (one_mul _).symm
      _ ≤ (X : ℝ) ^ 2 * Pa.N ^ ((3 : ℝ) / 2) := mul_le_mul_of_nonneg_right hX2 hN32nn
  have hA : (((2 * R + 1).toNat : ℝ)) ^ 2 ≤ 81 * ((X : ℝ) ^ 2 * Pa.N ^ ((3 : ℝ) / 2)) :=
    hRz2.trans (mul_le_mul_of_nonneg_left hNle (by norm_num))
  have hB : (((2 * R + 1).toNat : ℝ)) ^ 3 * (2 * (M : ℝ) + 1)
      ≤ 8019 * ((X : ℝ) ^ 2 * Pa.N ^ ((3 : ℝ) / 2)) := by
    have h := mul_le_mul hRz3 hM2 (by positivity : (0 : ℝ) ≤ 2 * (M : ℝ) + 1)
      (by positivity : (0 : ℝ) ≤ 729 * Pa.N ^ ((3 : ℝ) / 2))
    calc (((2 * R + 1).toNat : ℝ)) ^ 3 * (2 * (M : ℝ) + 1)
        ≤ (729 * Pa.N ^ ((3 : ℝ) / 2)) * (11 * (X : ℝ) ^ 2) := h
      _ = 8019 * ((X : ℝ) ^ 2 * Pa.N ^ ((3 : ℝ) / 2)) := by ring
  have hX2nn : (0 : ℝ) ≤ (X : ℝ) ^ 2 := by positivity
  calc ((((Work.FIPlan.gBox R).product (Work.FIPlan.gBox R)).filter
        (fun p : GaussianInt × GaussianInt => Work.FIPlan.absDelta p.1 p.2 < M)).card : ℝ)
      ≤ ((2 * R + 1).toNat : ℝ) ^ 2
          * (1 + ((2 * R + 1).toNat : ℝ) * (2 * (M : ℝ) + 1)) := htotal
    _ = ((2 * R + 1).toNat : ℝ) ^ 2
          + ((2 * R + 1).toNat : ℝ) ^ 3 * (2 * (M : ℝ) + 1) := by ring
    _ ≤ 81 * ((X : ℝ) ^ 2 * Pa.N ^ ((3 : ℝ) / 2))
          + 8019 * ((X : ℝ) ^ 2 * Pa.N ^ ((3 : ℝ) / 2)) := add_le_add hA hB
    _ = 8100 * ((X : ℝ) ^ 2 * Pa.N ^ ((3 : ℝ) / 2)) := by ring
    _ ≤ 100000 * ((X : ℝ) ^ 2 * Pa.N ^ ((3 : ℝ) / 2)) := by
        nlinarith [mul_nonneg hX2nn hN32nn]
    _ = 100000 * (X : ℝ) ^ 2 * Pa.N ^ ((3 : ℝ) / 2) := by ring

end Work.FIArea4.A4c
