import Mathlib
import Submission.Work.LinnikAreas.LocalCorr.sum_zmod_val_pow_eq

namespace Work.LinnikBurgess

/-- Reindexing the `2^g`-kernel sum: as `t` runs over `ZMod M`, the values
`C * (t.val : ZMod N)` (where `M * C = N`) run exactly once over the kernel
`{h : ZMod N // M * h = 0}`. -/
private lemma sum_kernel_reindex {N M C : ℕ} [NeZero N] [NeZero M]
    (hM : 0 < M) (hC : 0 < C) (hMC : M * C = N)
    (g : ZMod N → ℂ) :
    (∑ h ∈ Finset.univ.filter (fun h : ZMod N => ((M : ℕ) : ZMod N) * h = 0), g h)
      = ∑ t : ZMod M, g (((C : ℕ) : ZMod N) * (t.val : ZMod N)) := by
  have hCM : C * M = N := by rw [mul_comm, hMC]
  symm
  refine Finset.sum_bij (fun t (_ : t ∈ Finset.univ) =>
    ((C : ℕ) : ZMod N) * (t.val : ZMod N)) ?_ ?_ ?_ ?_
  · intro t _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← mul_assoc, ← Nat.cast_mul, hMC, ZMod.natCast_self, zero_mul]
  · intro t1 _ t2 _ heq
    have h1 : ((C * t1.val : ℕ) : ZMod N) = ((C * t2.val : ℕ) : ZMod N) := by
      simpa only [Nat.cast_mul] using heq
    have h2 : (C * t1.val) % N = (C * t2.val) % N :=
      (ZMod.natCast_eq_natCast_iff' (C * t1.val) (C * t2.val) N).mp h1
    have hv1 : C * t1.val < N := by
      rw [← hCM]; exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt t1) hC
    have hv2 : C * t2.val < N := by
      rw [← hCM]; exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt t2) hC
    rw [Nat.mod_eq_of_lt hv1, Nat.mod_eq_of_lt hv2] at h2
    exact ZMod.val_injective M (Nat.mul_left_cancel hC h2)
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
    have hcast : ((M : ℕ) : ZMod N) * h = ((M * h.val : ℕ) : ZMod N) := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val h]
    have hdvd : N ∣ M * h.val := by
      rw [hcast] at hh
      exact (CharP.cast_eq_zero_iff (ZMod N) N (M * h.val)).mp hh
    have hdvd' : M * C ∣ M * h.val := by rwa [hMC]
    obtain ⟨s, hs⟩ := (Nat.mul_dvd_mul_iff_left hM).mp hdvd'
    have hsM : s < M := by
      have hlt : C * s < C * M := by rw [← hs, hCM]; exact ZMod.val_lt h
      exact Nat.lt_of_mul_lt_mul_left hlt
    refine ⟨(s : ZMod M), Finset.mem_univ _, ?_⟩
    show ((C : ℕ) : ZMod N) * (((s : ZMod M)).val : ZMod N) = h
    rw [ZMod.val_natCast_of_lt hsM, ← Nat.cast_mul, ← hs, ZMod.natCast_zmod_val]
  · intro t _
    rfl

/-- Auxiliary form of the character sum over the `2^g`-kernel with abstract moduli
`M * C = N`. -/
private lemma twoPow_kernel_char_sum_aux {N M C : ℕ} [NeZero N] [NeZero M]
    (hM : 0 < M) (hC : 0 < C) (hMC : M * C = N) {θ : ℂ}
    (hθ : IsPrimitiveRoot θ N) (a : ZMod N) :
    (∑ h ∈ Finset.univ.filter (fun h : ZMod N => ((M : ℕ) : ZMod N) * h = 0),
      θ ^ ((a * h).val))
      = if M ∣ a.val then (M : ℂ) else 0 := by
  have hNpos : 0 < N := hMC ▸ Nat.mul_pos hM hC
  have hζ : IsPrimitiveRoot (θ ^ C) M :=
    hθ.pow hNpos (by rw [← hMC, mul_comm])
  have hterm : ∀ t : ZMod M,
      θ ^ ((a * (((C : ℕ) : ZMod N) * (t.val : ZMod N))).val)
        = (θ ^ C) ^ (((a.val : ZMod M) * t).val) := by
    intro t
    have hX : (a * (((C : ℕ) : ZMod N) * (t.val : ZMod N))).val
        = (a.val * C * t.val) % N := by
      have heq : a * (((C : ℕ) : ZMod N) * (t.val : ZMod N))
          = ((a.val * C * t.val : ℕ) : ZMod N) := by
        conv_lhs => rw [← ZMod.natCast_zmod_val a]
        push_cast
        ring
      rw [heq, ZMod.val_natCast]
    have hb : (((a.val : ZMod M)) * t).val = ((a.val % M) * t.val) % M := by
      rw [ZMod.val_mul, ZMod.val_natCast]
    have e1 : θ ^ ((a * (((C : ℕ) : ZMod N) * (t.val : ZMod N))).val)
        = θ ^ (a.val * C * t.val) := by
      rw [hX]
      exact pow_eq_pow_of_modEq (Nat.mod_modEq (a.val * C * t.val) N) hθ.pow_eq_one
    have e2 : θ ^ (a.val * C * t.val) = (θ ^ C) ^ (a.val * t.val) := by
      rw [← pow_mul, show C * (a.val * t.val) = a.val * C * t.val from by ring]
    have e3 : (θ ^ C) ^ (a.val * t.val) = (θ ^ C) ^ (((a.val : ZMod M) * t).val) := by
      refine pow_eq_pow_of_modEq ?_ hζ.pow_eq_one
      rw [hb]
      exact (Nat.ModEq.mul_right t.val (Nat.mod_modEq a.val M).symm).trans
        (Nat.mod_modEq ((a.val % M) * t.val) M).symm
    rw [e1, e2, e3]
  calc (∑ h ∈ Finset.univ.filter (fun h : ZMod N => ((M : ℕ) : ZMod N) * h = 0),
          θ ^ ((a * h).val))
      = ∑ t : ZMod M, θ ^ ((a * (((C : ℕ) : ZMod N) * (t.val : ZMod N))).val) :=
        sum_kernel_reindex hM hC hMC _
    _ = ∑ t : ZMod M, (θ ^ C) ^ (((a.val : ZMod M) * t).val) :=
        Finset.sum_congr rfl (fun t _ => hterm t)
    _ = if (a.val : ZMod M) = 0 then (M : ℂ) else 0 :=
        Work.LinnikAreas.LocalCorr.sum_zmod_val_pow_eq M hζ (a.val : ZMod M)
    _ = if M ∣ a.val then (M : ℂ) else 0 := by
        have hcf : ((a.val : ℕ) : ZMod M) = 0 ↔ M ∣ a.val :=
          CharP.cast_eq_zero_iff (ZMod M) M a.val
        by_cases h : ((a.val : ℕ) : ZMod M) = 0
        · rw [if_pos h, if_pos (hcf.mp h)]
        · rw [if_neg h, if_neg (fun hh => h (hcf.mpr hh))]

/-- **Character sum over the 2-power kernel.**  For `g ≤ K`, a primitive `2 ^ K`-th root of
unity `θ` and `a : ZMod (2 ^ K)`, the sum of `θ ^ (a * h).val` over the kernel
`H = {h : 2 ^ g * h = 0} = {h : 2 ^ (K - g) ∣ h.val}`, a subgroup of order `2 ^ g`, equals
`2 ^ g` when `2 ^ g ∣ a.val` and vanishes otherwise.

Proof route: `H` is the image of the injection `t ↦ 2 ^ (K - g) * t` from `ZMod (2 ^ g)` into
`ZMod (2 ^ K)`; reindexing gives `∑_{t : ZMod (2 ^ g)} θ ^ (a * 2 ^ (K - g) * t).val`, and with
`ζ := θ ^ (2 ^ (K - g))` (a primitive `2 ^ g`-th root of unity) each term equals
`ζ ^ (((a mod 2 ^ g) * t).val)`, so `Work.LinnikAreas.LocalCorr.sum_zmod_val_pow_eq` applies.
(Equivalently: `h ↦ θ ^ (a * h).val` is an additive character of `H`, trivial iff
`a * 2 ^ (K - g) = 0`, i.e. iff `2 ^ g ∣ a.val`.) -/
theorem twoPow_kernel_char_sum {K g : ℕ} (hg : g ≤ K)
    {θ : ℂ} (hθ : IsPrimitiveRoot θ (2 ^ K)) (a : ZMod (2 ^ K)) :
    (∑ h ∈ Finset.univ.filter (fun h : ZMod (2 ^ K)
        => ((2 ^ g : ℕ) : ZMod (2 ^ K)) * h = 0),
      θ ^ ((a * h).val))
      = if 2 ^ g ∣ a.val then ((2 ^ g : ℕ) : ℂ) else 0 := by
  haveI : NeZero (2 ^ K) := ⟨pow_ne_zero K (by norm_num)⟩
  haveI : NeZero (2 ^ g) := ⟨pow_ne_zero g (by norm_num)⟩
  have hMC : 2 ^ g * 2 ^ (K - g) = 2 ^ K := by
    rw [← pow_add, Nat.add_sub_of_le hg]
  exact twoPow_kernel_char_sum_aux (N := 2 ^ K) (M := 2 ^ g) (C := 2 ^ (K - g))
    (by positivity) (by positivity) hMC hθ a

end Work.LinnikBurgess
