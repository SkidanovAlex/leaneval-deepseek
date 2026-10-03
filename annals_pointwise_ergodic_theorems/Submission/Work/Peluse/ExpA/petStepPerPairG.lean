import Mathlib
import Submission.Work.Peluse.ExpA.sumExpCubeSlotFn
import Submission.Work.Peluse.PetLinear.linear_boxnorm_control_paper
import Submission.Work.Peluse.BoxNorm.boxNormPow_perm
import Submission.Work.Peluse.ExpA.slotArithBounds
import Submission.Work.Peluse.ExpA.boxNormPow_slotFn

set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped BigOperators

namespace Work.Peluse.ExpA

open Work.Peluse

noncomputable section

/-! ## Two small invariance lemmas -/

/-- Iterated conjugation does not change the norm. -/
lemma norm_starIterate (n : ℕ) (z : ℂ) : ‖(star^[n]) z‖ = ‖z‖ := by
  induction n with
  | zero => rw [Function.iterate_zero_apply]
  | succ m ih => rw [Function.iterate_succ_apply', norm_star, ih]

/-- Complex conjugation does not change the box-norm power. -/
lemma boxNormPow_starFn {t : ℕ} (Q : Fin t → Finset ℤ) (S : Finset ℤ) (g : ℤ → ℂ) :
    Work.Peluse.boxNormPow t Q S (fun x => star (g x)) = Work.Peluse.boxNormPow t Q S g := by
  rw [Work.Peluse.boxNormPow, Work.Peluse.boxNormPow, Work.Peluse.Pairing.boxSumPow_star,
    norm_star]

/-- The direction family of `linear_boxnorm_control_paper` at the slot coefficients `cSlot` is the
family displayed in the conclusion of the target. -/
lemma dirFamily_cSlot (s : ℕ) (c : ℤ) (u : Fin s → ℤ) (H : ℕ) :
    Work.Peluse.PetLinear.dirFamily (cSlot s c u) H
      = fun i : Fin (2 ^ s - 1) => Work.Peluse.arithIcc (c * dotU (ωOfA s i) u) H := by
  funext i
  exact congrArg (fun z : ℤ => Work.Peluse.arithIcc z H) (cSlot_last_sub s c u i)

/-! ## The target -/

/-- **The per-pair PET step in the paper's gauge.**  Same statement as `petStepPerPair`, but with
the extra hypothesis `CL * δ' ≤ γ ^ KL` relating the two parameters, which is exactly the gauge
`γ' ≤ γ^K / C` of Peluse's Lemma 4.10 (`Work.Peluse.PetLinear.linear_boxnorm_control_paper`).

The proof: the `a`-average of the cube terms is the multilinear average of the slot functions
(`sumExpCubeSlotFn`), so Lemma 4.10 applies at the level `2^s - 1` with the slot coefficients
`cSlot` and the slot functions `slotFn`; its conclusion is the box-norm power of the *last* slot
(all-ones) function at the direction family `cSlot last - cSlot i = c · dotU (ωOfA i) u` over the
enlarged window `symIcc (winN s C₀ N)`.  The last slot is a translate of `f` possibly composed with
conjugation (`boxNormPow_slotFn`), and the window is scaled down to `symIcc N`
(`boxNormPow_support_scaling`). -/
theorem petStepPerPairG {s : ℕ} (hs : 1 ≤ s) :
    ∃ KL : ℕ, 1 ≤ KL ∧ ∃ CL : ℝ, 0 < CL ∧
      ∀ (c : ℤ) (C₀ : ℕ) (N M₁ M₂ : ℕ) (b : Fin s → ℤ) (f : ℤ → ℂ)
        (k k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁}) {δ' γ : ℝ},
        0 < c → 1 ≤ N → 1 ≤ M₁ → 1 ≤ M₂ →
        (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c : ℝ) →
        (∀ i : Fin s, |b i| ≤ (C₀ : ℤ) * (N : ℤ) / (M₁ : ℤ)) →
        Work.Peluse.SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
        0 < δ' → 1 ≤ δ' * (M₂ : ℝ) →
        0 < γ → γ ≤ 1 → CL * δ' ≤ γ ^ KL →
        γ ≤ ‖((Work.Peluse.ExpA.winN s C₀ N : ℂ) * (M₂ : ℂ))⁻¹ *
            (∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
              Work.Peluse.Holds.ExpPET.expCube (fun i : Fin s => c * (a : ℤ) + b i)
                (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x)‖ ^ 2 →
        (γ / CL) ^ KL ≤ Work.Peluse.boxNormPow (2 ^ s - 1)
          (fun i : Fin (2 ^ s - 1) => Work.Peluse.arithIcc (c * Work.Peluse.ExpA.dotU
            (Work.Peluse.ExpA.ωOfA s i)
            (fun j => ((k j).1 : ℤ) - ((k' j).1 : ℤ))) (⌊δ' * (M₂ : ℝ)⌋).toNat)
          (Work.Peluse.symIcc N) f := by
  -- the level of Lemma 4.10 is `2^s - 1 ≥ 1`
  have hm : 0 < 2 ^ s - 1 := by
    have h : 1 < 2 ^ s := Nat.one_lt_two_pow (by omega)
    omega
  obtain ⟨K, hK1, C, hC0, hPET⟩ := Work.Peluse.PetLinear.linear_boxnorm_control_paper hm
  refine ⟨K, hK1, max C 1, by positivity, ?_⟩
  intro c C₀ N M₁ M₂ b f k k' δ' γ hc hN hM₁ hM₂ hNM hb hsup hbd hδ'0 hδ'M₂ hγ0 hγ1
    hgauge hmain
  -- the direction vector and the level
  let u : Fin s → ℤ := fun j => ((k j).1 : ℤ) - ((k' j).1 : ℤ)
  let H : ℕ := (⌊δ' * (M₂ : ℝ)⌋).toNat
  -- ## elementary bounds on the data
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hcM : c * (M₁ : ℤ) * (M₂ : ℤ) ≤ (N : ℤ) := by
    have hR : (M₁ : ℝ) * (M₂ : ℝ) * (c : ℝ) ≤ (N : ℝ) := by
      have h := (le_div_iff₀ hcR).mp hNM
      linarith [h]
    have hcast : (((c * (M₁ : ℤ) * (M₂ : ℤ) : ℤ)) : ℝ) ≤ ((N : ℤ) : ℝ) := by
      push_cast
      linarith [hR]
    exact_mod_cast hcast
  have hu_le : ∀ j : Fin s, |u j| ≤ (M₁ : ℤ) := by
    intro j
    have h1 : 1 ≤ (k j).1 := (Finset.mem_Icc.mp (k j).2).1
    have h2 : (k j).1 ≤ M₁ := (Finset.mem_Icc.mp (k j).2).2
    have h3 : 1 ≤ (k' j).1 := (Finset.mem_Icc.mp (k' j).2).1
    have h4 : (k' j).1 ≤ M₁ := (Finset.mem_Icc.mp (k' j).2).2
    show |((k j).1 : ℤ) - ((k' j).1 : ℤ)| ≤ (M₁ : ℤ)
    rw [abs_le]
    constructor <;> push_cast <;> omega
  -- ## the arithmetic bounds on the slot data
  obtain ⟨hdotB, hdotU, hcSlot, hsupp⟩ :=
    slotArithBounds (s := s) (C₀ := C₀) (M₁ := M₁) (M₂ := M₂) (N := N) (c := c)
      hc b u hM₁ hcM hb hu_le (f := f) hsup
  -- ## the slot functions are bounded by one
  have hFb : ∀ (j : Fin (2 ^ s - 1 + 1)) (x : ℤ), ‖slotFn s b u f j x‖ ≤ 1 := by
    intro j x
    rw [slotFn]
    exact le_trans (le_of_eq (norm_starIterate (weight (slotIdx s j))
      (f (x + dotB (slotIdx s j) b u)))) (hbd _)
  -- ## the cube average is the multilinear average of the slot functions
  have hfin : Work.Peluse.FinSuppZ f := Work.Peluse.FinSuppZ.of_supportIn hsup
  have hsumid : (∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
        Work.Peluse.Holds.ExpPET.expCube (fun i : Fin s => c * (a : ℤ) + b i)
          (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x)
      = ∑' x : ℤ, slotFn s b u f 0 x * ∑ a ∈ Finset.Icc 1 M₂,
          ∏ i : Fin (2 ^ s - 1), slotFn s b u f i.succ (x + cSlot s c u i.succ * (a : ℤ)) := by
    rw [sumExpCubeSlotFn (s := s) c b (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f M₂
      hfin]
    refine tsum_congr fun x => ?_
    rw [slotFn_zero]
  -- ## the hypothesis of Lemma 4.10
  have hLam : γ ≤ ‖((Work.Peluse.ExpA.winN s C₀ N : ℂ) * (M₂ : ℂ))⁻¹ *
      ∑' x : ℤ, slotFn s b u f 0 x * ∑ a ∈ Finset.Icc 1 M₂,
        ∏ i : Fin (2 ^ s - 1), slotFn s b u f i.succ (x + cSlot s c u i.succ * (a : ℤ))‖ ^ 2 := by
    rw [← hsumid]
    exact hmain
  -- ## the gauge
  have hgauge' : δ' ≤ γ ^ K / C := by
    have h1 : δ' ≤ γ ^ K / max C 1 :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < max C 1)).mpr (by linarith [hgauge])
    have h2 : γ ^ K / max C 1 ≤ γ ^ K / C :=
      div_le_div_of_nonneg_left (pow_nonneg hγ0.le K) hC0 (le_max_left C 1)
    linarith
  -- ## Lemma 4.10
  have hWpos : 0 < Work.Peluse.ExpA.winN s C₀ N :=
    lt_of_lt_of_le Nat.zero_lt_one (le_trans hN (le_winN s C₀ N))
  have hM2pos : 0 < M₂ := by omega
  have hHge : 1 ≤ H := by
    have h0 : (0 : ℤ) ≤ ⌊δ' * (M₂ : ℝ)⌋ := Int.floor_nonneg.mpr (by linarith [hδ'M₂])
    have h1 : (1 : ℤ) ≤ ⌊δ' * (M₂ : ℝ)⌋ := by
      have hle : ((1 : ℤ) : ℝ) ≤ δ' * (M₂ : ℝ) := by push_cast; linarith [hδ'M₂]
      exact_mod_cast (Int.le_floor.mpr hle)
    have htoNat : ((⌊δ' * (M₂ : ℝ)⌋).toNat : ℤ) = ⌊δ' * (M₂ : ℝ)⌋ :=
      Int.toNat_of_nonneg h0
    show 1 ≤ H
    omega
  have hcore := hPET (cSlot s c u) (cSlot_zero s c u) (N := Work.Peluse.ExpA.winN s C₀ N)
    (M := M₂) hWpos hM2pos (slotFn s b u f) (γ := γ) (γ' := δ') hγ0 hδ'0 hγ1 hFb
    (fun j => hsupp j) (fun y hy j => hcSlot j y hy) hgauge' hHge hLam
  -- ## transferring the conclusion to the datum's objects
  have hfun : Work.Peluse.boxNormPow (2 ^ s - 1)
        (fun i : Fin (2 ^ s - 1) => Work.Peluse.arithIcc (c * dotU (ωOfA s i) u) H)
        (Work.Peluse.symIcc (Work.Peluse.ExpA.winN s C₀ N)) (slotFn s b u f (Fin.last (2 ^ s - 1)))
      = Work.Peluse.boxNormPow (2 ^ s - 1)
        (fun i : Fin (2 ^ s - 1) => Work.Peluse.arithIcc (c * dotU (ωOfA s i) u) H)
        (Work.Peluse.symIcc (Work.Peluse.ExpA.winN s C₀ N)) f :=
    boxNormPow_slotFn _ _ b u hfin _
  have hscale : Work.Peluse.boxNormPow (2 ^ s - 1)
        (fun i : Fin (2 ^ s - 1) => Work.Peluse.arithIcc (c * dotU (ωOfA s i) u) H)
        (Work.Peluse.symIcc (Work.Peluse.ExpA.winN s C₀ N)) f
      ≤ Work.Peluse.boxNormPow (2 ^ s - 1)
        (fun i : Fin (2 ^ s - 1) => Work.Peluse.arithIcc (c * dotU (ωOfA s i) u) H)
        (Work.Peluse.symIcc N) f := by
    have hcardN : 0 < (Work.Peluse.symIcc N).card := by
      rw [Work.Peluse.PetLinear.symIcc_card]; omega
    have hcard : (Work.Peluse.symIcc N).card
        ≤ (Work.Peluse.symIcc (Work.Peluse.ExpA.winN s C₀ N)).card := by
      rw [Work.Peluse.PetLinear.symIcc_card, Work.Peluse.PetLinear.symIcc_card]
      have := le_winN s C₀ N
      omega
    rw [Work.Peluse.PetLinear.boxNormPow_support_scaling _ (Work.Peluse.symIcc N)
      (Work.Peluse.symIcc (Work.Peluse.ExpA.winN s C₀ N)) f hcardN]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    have hc2 : (0 : ℝ) < ((Work.Peluse.symIcc (Work.Peluse.ExpA.winN s C₀ N)).card : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le hcardN hcard)
    rw [← div_eq_mul_inv, div_le_one hc2]
    exact_mod_cast hcard
  have hkey : (γ / C) ^ K ≤ Work.Peluse.boxNormPow (2 ^ s - 1)
      (fun i : Fin (2 ^ s - 1) => Work.Peluse.arithIcc (c * dotU (ωOfA s i) u) H)
      (Work.Peluse.symIcc N) f := by
    calc (γ / C) ^ K
        ≤ Work.Peluse.boxNormPow (2 ^ s - 1) (Work.Peluse.PetLinear.dirFamily (cSlot s c u) H)
            (Work.Peluse.symIcc (Work.Peluse.ExpA.winN s C₀ N))
            (slotFn s b u f (Fin.last (2 ^ s - 1))) := hcore
      _ = Work.Peluse.boxNormPow (2 ^ s - 1)
            (fun i : Fin (2 ^ s - 1) => Work.Peluse.arithIcc (c * dotU (ωOfA s i) u) H)
            (Work.Peluse.symIcc (Work.Peluse.ExpA.winN s C₀ N))
            (slotFn s b u f (Fin.last (2 ^ s - 1))) := by rw [dirFamily_cSlot]
      _ = Work.Peluse.boxNormPow (2 ^ s - 1)
            (fun i : Fin (2 ^ s - 1) => Work.Peluse.arithIcc (c * dotU (ωOfA s i) u) H)
            (Work.Peluse.symIcc (Work.Peluse.ExpA.winN s C₀ N)) f := hfun
      _ ≤ Work.Peluse.boxNormPow (2 ^ s - 1)
            (fun i : Fin (2 ^ s - 1) => Work.Peluse.arithIcc (c * dotU (ωOfA s i) u) H)
            (Work.Peluse.symIcc N) f := hscale
  have hdiv : (γ / max C 1) ^ K ≤ (γ / C) ^ K :=
    pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_left hγ0.le hC0 (le_max_left C 1)) K
  exact le_trans hdiv hkey

end

end Work.Peluse.ExpA
