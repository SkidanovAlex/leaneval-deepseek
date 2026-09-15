import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.Set.Card
import Submission.Commons.Data.Fintype.card_subtype_ne

namespace Commons.Data.Nat

open Finset

/-- **Solution count of a one-variable linear congruence.** For `Q > 0` and `A ≠ 0`, the number
of `x ∈ [0, Q)` with `Q ∣ A x - c` is at most `|A|`.  (Local copy of a bound that is also being
developed separately; kept here so the slab count is self-contained.)

Proof: the map `x ↦ |A| x / Q` is strictly increasing along the solutions, because for two distinct
solutions `x < x'` one has `0 < x' - x < Q` and `Q ∣ A (x' - x)`, which forces
`Q ≤ |A| (x' - x)`; hence `|A| x / Q < |A| x' / Q`.  This injects the solution set into
`{0, …, |A| - 1}`. -/
private theorem sol_linear_congr_card_le {Q : ℕ} (hQ : 0 < Q) (A c : ℤ) (hA : A ≠ 0) :
    ((Finset.univ : Finset (Fin Q)).filter (fun x => (Q : ℤ) ∣ (A * (x.val : ℤ) - c))).card
      ≤ A.natAbs := by
  classical
  have hAn : 0 < A.natAbs := Int.natAbs_pos.mpr hA
  set K : Finset (Fin Q) := (Finset.univ : Finset (Fin Q)).filter
      (fun x => (Q : ℤ) ∣ (A * (x.val : ℤ) - c)) with hK
  set ψ : Fin Q → ℕ := fun x => A.natAbs * x.val / Q with hψ
  have hgap : ∀ x y : Fin Q, x ∈ K → y ∈ K → x.val < y.val →
      Q ≤ A.natAbs * (y.val - x.val) := by
    intro x y hx hy hlt
    rw [hK, Finset.mem_filter] at hx hy
    obtain ⟨_, hxdiv⟩ := hx
    obtain ⟨_, hydiv⟩ := hy
    obtain ⟨k, hk⟩ := hxdiv
    obtain ⟨l, hl⟩ := hydiv
    have hdiff : A * ((y.val : ℤ) - (x.val : ℤ)) = (Q : ℤ) * (l - k) := by
      have h1 : A * ((y.val : ℤ) - (x.val : ℤ))
          = (A * (y.val : ℤ) - c) - (A * (x.val : ℤ) - c) := by ring
      rw [h1, hl, hk]; ring
    have hcast : ((y.val : ℤ) - (x.val : ℤ)) = ((y.val - x.val : ℕ) : ℤ) :=
      (Nat.cast_sub (le_of_lt hlt)).symm
    rw [hcast] at hdiff
    have hyx : ((y.val - x.val : ℕ) : ℤ) ≠ 0 := by
      simp only [ne_eq, Int.natCast_eq_zero]
      omega
    have hne : (l - k) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hdiff
      exact (mul_ne_zero hA hyx) hdiff
    have hnat : A.natAbs * (y.val - x.val) = Q * (l - k).natAbs := by
      have h2 := congrArg Int.natAbs hdiff
      rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_natCast] at h2
      exact h2
    rw [hnat]
    have hle1 : 1 ≤ (l - k).natAbs := by
      have : 0 < (l - k).natAbs := Int.natAbs_pos.mpr hne
      omega
    calc Q = Q * 1 := (mul_one Q).symm
      _ ≤ Q * (l - k).natAbs := Nat.mul_le_mul_left Q hle1
  have hmono : ∀ x y : Fin Q, x ∈ K → y ∈ K → x.val < y.val → ψ x < ψ y := by
    intro x y hx hy hlt
    have hg := hgap x y hx hy hlt
    have hxle : x.val ≤ y.val := le_of_lt hlt
    have hsplit : A.natAbs * y.val = A.natAbs * x.val + A.natAbs * (y.val - x.val) := by
      rw [← Nat.mul_add, Nat.add_sub_of_le hxle]
    have hge : A.natAbs * x.val + Q ≤ A.natAbs * y.val := by
      rw [hsplit]; exact Nat.add_le_add_left hg _
    have hdiv : (A.natAbs * x.val + Q) / Q = A.natAbs * x.val / Q + 1 := by
      simpa using Nat.add_mul_div_left (A.natAbs * x.val) 1 hQ
    rw [hψ]
    calc A.natAbs * x.val / Q
        < (A.natAbs * x.val + Q) / Q := by rw [hdiv]; exact Nat.lt_succ_self _
      _ ≤ A.natAbs * y.val / Q := Nat.div_le_div_right hge
  have hinj : Set.InjOn ψ ↑K := by
    intro x hx y hy hxy
    rw [Finset.mem_coe] at hx hy
    rcases lt_trichotomy x y with hlt | heq | hgt
    · exfalso
      have h := hmono x y hx hy (by rwa [Fin.lt_def] at hlt)
      rw [hxy] at h
      exact absurd h (lt_irrefl _)
    · exact heq
    · exfalso
      have h := hmono y x hy hx (by rwa [Fin.lt_def] at hgt)
      rw [hxy] at h
      exact absurd h (lt_irrefl _)
  have hmap : Set.MapsTo ψ ↑K ↑(Finset.range A.natAbs) := by
    intro x hx
    rw [Finset.mem_coe] at hx
    rw [Finset.mem_coe, Finset.mem_range, hψ]
    rw [Nat.div_lt_iff_lt_mul hQ]
    exact Nat.mul_lt_mul_of_pos_left x.isLt hAn
  calc K.card ≤ (Finset.range A.natAbs).card := Finset.card_le_card_of_injOn ψ hmap hinj
    _ = A.natAbs := Finset.card_range _

/-- **Reduction of a window condition modulo `Q`.**  If `S` lies within `K` of `θ + Q ℤ`, then so
does its residue `S % Q`. -/
private lemma emod_window {Q : ℕ} (S : ℤ) (θ K : ℝ)
    (h : ∃ z : ℤ, |(S : ℝ) - (z : ℝ) * (Q : ℝ) - θ| ≤ K) :
    ∃ z : ℤ, |(((S % (Q : ℤ) : ℤ)) : ℝ) - (z : ℝ) * (Q : ℝ) - θ| ≤ K := by
  obtain ⟨z, hz⟩ := h
  refine ⟨z - S / (Q : ℤ), ?_⟩
  have hS : (S : ℝ) = ((S % (Q : ℤ) : ℤ) : ℝ)
      + (Q : ℝ) * ((S / (Q : ℤ) : ℤ) : ℝ) := by
    have hh := Int.mul_ediv_add_emod S (Q : ℤ)
    have key : (S : ℝ) = (Q : ℝ) * ((S / (Q : ℤ) : ℤ) : ℝ)
        + ((S % (Q : ℤ) : ℤ) : ℝ) := by
      have hcast : ((S : ℤ) : ℝ) = (((Q : ℤ) * (S / (Q : ℤ)) + S % (Q : ℤ) : ℤ) : ℝ) := by
        rw [hh]
      push_cast at hcast
      exact hcast
    linarith [key]
  have heq : (S : ℝ) - (z : ℝ) * (Q : ℝ) - θ
      = ((S % (Q : ℤ) : ℤ) : ℝ) - ((z - S / (Q : ℤ) : ℤ) : ℝ) * (Q : ℝ) - θ := by
    rw [hS]; push_cast; ring
  rw [← heq]; exact hz

/-- The linear form splits into the `j₀`-coordinate and the sum over the remaining coordinates. -/
private lemma sum_split {t Q : ℕ} (L : Fin t → ℤ) (j₀ : Fin t) (u : Fin t → Fin Q) :
    (∑ j, L j * ((u j).val : ℤ))
      = L j₀ * ((u j₀).val : ℤ)
        + ∑ i : {i : Fin t // i ≠ j₀}, L i.1 * ((u i.1).val : ℤ) := by
  rw [← Finset.add_sum_erase Finset.univ (fun j => L j * ((u j).val : ℤ)) (Finset.mem_univ j₀)]
  congr 1
  exact Finset.sum_subtype (Finset.univ.erase j₀) (fun x => by simp [Finset.mem_erase])
    (fun j => L j * ((u j).val : ℤ))

/-- **Slab count for a linear congruence mod `Q`.**  Fix a nonzero coordinate `L j₀` of the integer
vector `L`.  The number of `u : Fin t → Fin Q` for which `Σ(u) = ∑_j L j * u_j` lies within `K` of
`θ + Q ℤ` (i.e. `Σ(u) mod Q` lies in a fixed window of `W.card` residues) is at most
`Q^(t-1) * (W.card * |L j₀|)`.

Proof sketch: the condition `∃ z, |Σ(u) - z Q - θ| ≤ K` depends only on `Σ(u) mod Q` (write
`Σ(u) = z₀ Q + s` with `0 ≤ s < Q`: then it is equivalent to `∃ z, |s - z Q - θ| ≤ K`).  By `hcond`
this forces `s ∈ W`.  Fix all coordinates except `j₀`: then `Σ(u) = R + L j₀ * x` with `R` fixed, so
the condition is `L j₀ * x ≡ w - R (mod Q)` for some `w ∈ W`; for each `w` the congruence has at
most `|L j₀|` solutions `x ∈ [0,Q)` (by the same argument as in the requested lemma
`Commons.Data.Nat.card_sol_linear_congr_le`), and there are `W.card` of them.  Summing over the
`Q^(t-1)` choices of the other coordinates gives the claim. -/
theorem card_mod_window_le {t : ℕ} (L : Fin t → ℤ) (j₀ : Fin t) (hj₀ : L j₀ ≠ 0) {Q : ℕ}
    (hQ : 0 < Q) (W : Finset ℤ) (hW : ∀ r ∈ W, 0 ≤ r ∧ r < (Q : ℤ)) (θ K : ℝ)
    (hcond : ∀ r : ℤ, 0 ≤ r → r < (Q : ℤ) →
        (∃ z : ℤ, |(r : ℝ) - (z : ℝ) * (Q : ℝ) - θ| ≤ K) → r ∈ W) :
    Set.ncard {u : Fin t → Fin Q |
        ∃ z : ℤ, |(((∑ j, L j * ((u j).val : ℤ) : ℤ)) : ℝ) - (z : ℝ) * (Q : ℝ) - θ| ≤ K}
      ≤ Q ^ (t - 1) * (W.card * (L j₀).natAbs) := by
  classical
  set T : Finset (Fin t → Fin Q) := Finset.univ.filter
      (fun u => ∃ z : ℤ,
        |(((∑ j, L j * ((u j).val : ℤ) : ℤ)) : ℝ) - (z : ℝ) * (Q : ℝ) - θ| ≤ K) with hT
  have hset : {u : Fin t → Fin Q |
        ∃ z : ℤ, |(((∑ j, L j * ((u j).val : ℤ) : ℤ)) : ℝ) - (z : ℝ) * (Q : ℝ) - θ| ≤ K}
      = (↑T : Set (Fin t → Fin Q)) := by
    ext u; simp [hT]
  rw [hset, Set.ncard_coe_finset]
  set r : (Fin t → Fin Q) → ({i : Fin t // i ≠ j₀} → Fin Q) := fun u i => u i.1 with hr
  have hfiber : ∀ b ∈ T.image r,
      (T.filter (fun u => r u = b)).card ≤ W.card * (L j₀).natAbs := by
    intro b hb
    set Fb : Finset (Fin t → Fin Q) := T.filter (fun u => r u = b) with hFb
    have hres : Set.MapsTo (fun u : Fin t → Fin Q => (∑ j, L j * ((u j).val : ℤ)) % (Q : ℤ))
        ↑Fb ↑W := by
      intro u hu
      rw [Finset.mem_coe, hFb, Finset.mem_filter] at hu
      obtain ⟨huT, _⟩ := hu
      rw [hT, Finset.mem_filter] at huT
      obtain ⟨_, huP⟩ := huT
      have hred := emod_window (Q := Q) (∑ j, L j * ((u j).val : ℤ)) θ K huP
      exact hcond _ (Int.emod_nonneg _ (by exact_mod_cast ne_of_gt hQ))
        (Int.emod_lt_of_pos _ (by exact_mod_cast hQ)) hred
    have hcard : Fb.card = ∑ w ∈ W,
        (Fb.filter (fun u => (∑ j, L j * ((u j).val : ℤ)) % (Q : ℤ) = w)).card :=
      Finset.card_eq_sum_card_fiberwise hres
    rw [hcard]
    calc ∑ w ∈ W, (Fb.filter (fun u => (∑ j, L j * ((u j).val : ℤ)) % (Q : ℤ) = w)).card
        ≤ ∑ _w ∈ W, (L j₀).natAbs := by
          apply Finset.sum_le_sum
          intro w hw
          set Dw : Finset (Fin t → Fin Q) :=
              Fb.filter (fun u => (∑ j, L j * ((u j).val : ℤ)) % (Q : ℤ) = w) with hDw
          set R : ℤ := ∑ i : {i : Fin t // i ≠ j₀}, L i.1 * ((b i).val : ℤ) with hR
          have hmap2 : Set.MapsTo (fun u : Fin t → Fin Q => u j₀) ↑Dw
              ↑((Finset.univ : Finset (Fin Q)).filter
                  (fun x => (Q : ℤ) ∣ L j₀ * (x.val : ℤ) - (w - R))) := by
            intro u hu
            rw [Finset.mem_coe, hDw, Finset.mem_filter] at hu
            obtain ⟨huFb, huW⟩ := hu
            rw [hFb, Finset.mem_filter] at huFb
            obtain ⟨_, hur⟩ := huFb
            rw [Finset.mem_coe, Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_⟩
            have hsplit := sum_split L j₀ u
            have hRb : (∑ i : {i : Fin t // i ≠ j₀}, L i.1 * ((u i.1).val : ℤ)) = R := by
              rw [hR]
              apply Finset.sum_congr rfl
              intro i _
              have hi : u i.1 = b i := by
                have := congrFun hur i
                simpa [hr] using this
              rw [hi]
            have hS : (∑ j, L j * ((u j).val : ℤ)) = L j₀ * ((u j₀).val : ℤ) + R := by
              rw [hsplit, hRb]
            have hdvd : (Q : ℤ) ∣ (∑ j, L j * ((u j).val : ℤ)) - w := by
              have hroot : (Q : ℤ) ∣ (∑ j, L j * ((u j).val : ℤ))
                  - (∑ j, L j * ((u j).val : ℤ)) % (Q : ℤ) := by
                refine ⟨(∑ j, L j * ((u j).val : ℤ)) / (Q : ℤ), ?_⟩
                have hh := Int.mul_ediv_add_emod (∑ j, L j * ((u j).val : ℤ)) (Q : ℤ)
                linarith [hh]
              rw [← huW]; exact hroot
            have heq : L j₀ * ((u j₀).val : ℤ) - (w - R)
                = (∑ j, L j * ((u j).val : ℤ)) - w := by
              rw [hS]; ring
            rw [heq]; exact hdvd
          have hinj2 : Set.InjOn (fun u : Fin t → Fin Q => u j₀) ↑Dw := by
            intro u hu v hv huv
            rw [Finset.mem_coe, hDw, Finset.mem_filter] at hu hv
            obtain ⟨huFb, _⟩ := hu
            obtain ⟨hvFb, _⟩ := hv
            rw [hFb, Finset.mem_filter] at huFb hvFb
            obtain ⟨_, hur⟩ := huFb
            obtain ⟨_, hvr⟩ := hvFb
            funext k
            by_cases hk : k = j₀
            · subst hk; exact huv
            · have h1 : r u ⟨k, hk⟩ = r v ⟨k, hk⟩ := by rw [hur, hvr]
              simpa [hr] using h1
          calc Dw.card ≤ ((Finset.univ : Finset (Fin Q)).filter
                  (fun x => (Q : ℤ) ∣ L j₀ * (x.val : ℤ) - (w - R))).card :=
                Finset.card_le_card_of_injOn _ hmap2 hinj2
            _ ≤ (L j₀).natAbs := sol_linear_congr_card_le hQ (L j₀) (w - R) hj₀
      _ = W.card * (L j₀).natAbs := by simp [Finset.sum_const]
  have hmain := Finset.card_le_mul_card_image (f := r) T (W.card * (L j₀).natAbs) hfiber
  have himg : (T.image r).card ≤ Q ^ (t - 1) := by
    calc (T.image r).card ≤ (Finset.univ : Finset ({i : Fin t // i ≠ j₀} → Fin Q)).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card ({i : Fin t // i ≠ j₀} → Fin Q) := Finset.card_univ
      _ = Fintype.card (Fin Q) ^ Fintype.card {i : Fin t // i ≠ j₀} := Fintype.card_fun
      _ = Q ^ (t - 1) := by
            rw [Fintype.card_fin, Commons.Data.Fintype.card_subtype_ne, Fintype.card_fin]
  calc T.card ≤ (W.card * (L j₀).natAbs) * (T.image r).card := hmain
    _ ≤ (W.card * (L j₀).natAbs) * Q ^ (t - 1) := Nat.mul_le_mul_left _ himg
    _ = Q ^ (t - 1) * (W.card * (L j₀).natAbs) := Nat.mul_comm _ _

end Commons.Data.Nat