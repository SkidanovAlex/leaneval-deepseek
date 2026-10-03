import Mathlib
import Submission.Work.Peluse.Prop36SW.roundDefs
import Submission.Work.Peluse.Prop36SW.flatDefs
import Submission.Work.Peluse.Prop36SW.pDir_eq_dir_gen
import Submission.Work.Peluse.Prop36SW.boxNormPow_le_boxNorm
import Submission.Work.Peluse.Prop36SW.average_piIcc_eq_average_paramBox

/-!
# The vocabulary of the §5 round's *regrouping* step

See `NOTES_prop36SW_of_ladderA_SESSION7.md` §3 step 5 and `NOTES_prop36SW_of_ladderA_SESSION8.md`.

The round `n+1 → n` of the §5 chain reindexes a box-norm family indexed by the slots
`Σ s : D.S (n+2), Fin (t s)` onto the family `FamIdx (regroupKω D (n+1) t)` indexed by the
nonempty subsets `ω` of the *new* slots `D.S (n+1)`, the slot `s` being grouped into the subset
`parSet D (n+1) s`.  This module holds the definitions and the elementary lemmas of that step:

* `slotOf`, `parSet` — the canonical slot `(x, 0)` and the slot set over `D.par m s`;
* `slotOf_fst`, `image_slotOf_fst`, `image_fst_slotOf` — the two-way correspondence between the
  finite sets `s ⊆ D.S m` and `s.image slotOf ⊆ Slot (D.S m) 1`;
* `regroupKω_eq_fiber_sum` — the regrouping multiplicity is the fibre sum;
* `pFlat_encD`, `dir_eq_zero_of_lt`, `pFlat_splitUpd_eq_sum_slot` — the *direction identity* of the
  round, i.e. the level-`(n+1)` coefficient of a slot read through its parent;
* `boxNormPow_le_boxNorm'`, `average_Abox_eq_average_parBox` — the passage from the box-norm power
  to the box norm, and the flat/dependent box-average transfer.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse.UControl

/-- `pFlat` read at an encoded parameter: the signed direction decayed to the dependent family. -/
theorem pFlat_encD (D : IdxDatum) (d : ℕ) (c : ℤ) (m Λ : ℕ) (s : D.S (m + 1))
    (a : D.Idx (m + 1)) :
    pFlat D d c m Λ s (encD D (m + 1) a)
      = (Λ : ℤ) * ((d : ℤ) - (m : ℤ)) * D.dir d c m (D.par m s) (D.pad (m + 1) a) := by
  rw [pFlat, decD_encD]

/-- `dir` vanishes above the degree of `P`. -/
theorem dir_eq_zero_of_lt (D : IdxDatum) (d : ℕ) (c : ℤ) :
    ∀ (j : ℕ) (i : D.I j) (a : (j' : ℕ) → D.S j' → ℤ), d < j → D.dir d c j i a = 0 := by
  intro j
  induction j with
  | zero => intro i a h; omega
  | succ j ih =>
      intro i a h
      rw [dir_succ_eq_sum_slotCoeff D d c j i a]
      refine Finset.sum_eq_zero fun s _ => ?_
      rcases lt_or_ge d j with hj | hj
      · rw [slotCoeff, ih (D.par j s) a hj]; simp
      · have hdj : (d : ℤ) - (j : ℤ) = 0 := by omega
        rw [slotCoeff, hdj]; simp

/-- **The round's direction identity.**  The level-`(n+1)` direction of a level-`(n+2)` slot is the
sum, over the slots of its parent, of the level-`n` directions times the level-`(n+1)` parameters. -/
theorem pFlat_splitUpd_eq_sum_slot (D : IdxDatum) (d : ℕ) (c : ℤ) (n Λ : ℕ)
    (al : D.Idx (n + 1)) (b : D.S (n + 1) → ℤ) (s : D.S (n + 2)) :
    pFlat D d c (n + 1) Λ s (encD D (n + 2) (splitUpd D n al b))
      = ∑ s' ∈ (D.par (n + 1) s).1,
          pFlat D d c n (Λ * (d - (n + 1))) s' (encD D (n + 1) al) * b s' := by
  by_cases hnd : n + 1 ≤ d
  · rw [pFlat_encD, pad_splitUpd,
      dir_succ_eq_sum_slotCoeff D d c n (D.par (n + 1) s) (padUpdate D n al b), Finset.mul_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [slotCoeff, padUpdate_at, pFlat_encD,
      dir_congr D d c n (D.par n s') (padUpdate D n al b) (D.pad (n + 1) al)
        (fun j' hj' t => padUpdate_of_ne D n al b (by omega) t)]
    have hcast : ((Λ * (d - (n + 1)) : ℕ) : ℤ) = (Λ : ℤ) * ((d : ℤ) - (n + 1)) := by
      rw [Nat.cast_mul, Nat.cast_sub hnd]; push_cast; ring
    rw [hcast]; push_cast; ring
  · have hΛ0 : Λ * (d - (n + 1)) = 0 := by
      have : d - (n + 1) = 0 := by omega
      rw [this, mul_zero]
    rw [pFlat_encD, pad_splitUpd,
      dir_eq_zero_of_lt D d c (n + 1) (D.par (n + 1) s) (padUpdate D n al b) (by omega)]
    simp only [mul_zero]
    rw [hΛ0]
    refine (Finset.sum_eq_zero fun s' _ => ?_).symm
    rw [pFlat]; simp

/-- **The box-norm power is at most the box norm**, for every level (the level `0` case being an
equality). -/
theorem boxNormPow_le_boxNorm' {t : ℕ} {Q : Fin t → Finset ℤ} {S : Finset ℤ} {f : ℤ → ℂ}
    (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) (hs : ∀ x : ℤ, x ∉ S → f x = 0) :
    Work.Peluse.boxNormPow t Q S f ≤ Work.Peluse.boxNorm t Q S f := by
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht
    rw [Work.Peluse.boxNorm]
    norm_num
  · exact boxNormPow_le_boxNorm ht hf hs

/-- **The flat box average is the dependent box average**: `Abox D l H` is the image of
`D.parBox l H` under `encD`, on which `decD` is a two-sided inverse. -/
theorem average_Abox_eq_average_parBox (D : IdxDatum) (l H : ℕ) (Ψ : D.Idx l → ℝ) :
    ((Abox D l H).card : ℝ)⁻¹ * ∑ a ∈ Abox D l H, Ψ (decD D l a)
      = ((D.parBox l H).card : ℝ)⁻¹ * ∑ a ∈ D.parBox l H, Ψ a := by
  rw [card_Abox, Abox,
    Finset.sum_image (f := fun a => Ψ (decD D l a)) (g := encD D l)
      (Set.injOn_of_injective (encD_injective D l))]
  simp only [decD_encD]

/-- The canonical slot `(x, 0)`. -/
abbrev slotOf {ι : Type} (x : ι) : Slot ι (fun _ => 1) := ⟨x, 0⟩

/-- The set of slots over a nonempty subset of `D.S m`, as a slot set. -/
def parSet (D : IdxDatum) (m : ℕ) (s : D.S (m + 1)) : SlotSet (D.S m) (fun _ => 1) :=
  ⟨(D.par m s).1.image (fun x => slotOf x), Finset.image_nonempty.mpr (D.par m s).2⟩

/-- The canonical slot of a slot set is `(x, 0)`. -/
theorem slotOf_fst {ι : Type} (x : Slot ι (fun _ => 1)) : slotOf x.1 = x := by
  obtain ⟨a, b⟩ := x
  have hb : b = 0 := Subsingleton.elim b 0
  rw [hb]

/-- `(s.image (·,0)).image (·.1) = s`. -/
theorem image_slotOf_fst {ι : Type} [DecidableEq ι] (s : Finset ι) :
    (s.image (fun x => slotOf x)).image (fun σ => σ.1) = s := by
  rw [Finset.image_image]
  rw [show ((fun σ : Slot ι (fun _ => 1) => σ.1) ∘ (fun x => slotOf x)) = (id : ι → ι) from
        funext fun x => rfl]
  exact Finset.image_id

/-- `(s.image (·.1)).image (·,0) = s` for a slot set. -/
theorem image_fst_slotOf {ι : Type} [DecidableEq ι] (s : Finset (Slot ι (fun _ => 1))) :
    (s.image (fun σ => σ.1)).image (fun x => slotOf x) = s := by
  rw [Finset.image_image]
  rw [show ((fun x => slotOf x) ∘ (fun σ : Slot ι (fun _ => 1) => σ.1))
        = (id : Slot ι (fun _ => 1) → Slot ι (fun _ => 1)) from
        funext fun σ => slotOf_fst σ]
  exact Finset.image_id

/-- **The regrouping multiplicity is the fibre sum**: `regroupKω` counts the multiplicities of the
slots over each slot set. -/
theorem regroupKω_eq_fiber_sum (D : IdxDatum) (m : ℕ) (k : D.S (m + 1) → ℕ)
    (ω : SlotSet (D.S m) (fun _ => 1)) :
    regroupKω D m k ω
      = ∑ s ∈ Finset.univ.filter (fun s : D.S (m + 1) => parSet D m s = ω), k s := by
  rw [regroupKω]
  have hfilt : (Finset.univ.filter (fun s : D.S (m + 1) =>
        D.par m s = ⟨ω.1.image (fun x => x.1), Finset.image_nonempty.mpr ω.2⟩))
      = Finset.univ.filter (fun s : D.S (m + 1) => parSet D m s = ω) := by
    refine Finset.filter_congr fun s _ => ?_
    constructor
    · intro h
      have hv : (D.par m s).1 = ω.1.image (fun x => x.1) := congrArg Subtype.val h
      refine Subtype.ext ?_
      show (D.par m s).1.image (fun x => slotOf x) = ω.1
      rw [hv, image_fst_slotOf]
    · intro h
      have hv : (D.par m s).1.image (fun x => slotOf x) = ω.1 := congrArg Subtype.val h
      refine Subtype.ext ?_
      show (D.par m s).1 = ω.1.image (fun x => x.1)
      conv_rhs => rw [← hv]
      exact (image_slotOf_fst (D.par m s).1).symm
  rw [hfilt]

/-- `slotOf` is injective. -/
theorem slotOf_injective {ι : Type} : Function.Injective (slotOf (ι := ι)) :=
  fun _ _ h => congrArg (fun σ : Slot ι (fun _ => 1) => σ.1) h

/-- Reindexing a sum over `s.image slotOf` back to a sum over `s`. -/
theorem sum_image_slotOf {ι : Type} [DecidableEq ι] (s : Finset ι)
    (F : Slot ι (fun _ => 1) → ℤ) :
    (∑ t ∈ s.image (fun x => slotOf x), F t) = ∑ x ∈ s, F (slotOf x) := by
  rw [Finset.sum_image (f := F) (g := fun x => slotOf x)
    (fun _ _ _ _ h => slotOf_injective h)]

/-- **The average over the `piFinset` box is the average over the ladder's `paramBox`**, in the
orientation used by the chain (the `paramBox` side carries the `(·,0)`-slot of the `piFinset`
side). -/
theorem avg_piIcc_eq_avg_paramBox {ι : Type} [Fintype ι] [DecidableEq ι] (M : ℕ)
    (Φ : (ι → ℤ) → ℝ) :
    ((Fintype.piFinset (fun _ : ι => Finset.Icc (-(M : ℤ)) (M : ℤ))).card : ℝ)⁻¹ *
        ∑ b ∈ Fintype.piFinset (fun _ : ι => Finset.Icc (-(M : ℤ)) (M : ℤ)), Φ b
      = ((paramBox (k := fun _ : ι => 1) (M + 1)).card : ℝ)⁻¹ *
        ∑ b ∈ paramBox (k := fun _ : ι => 1) (M + 1), Φ (fun x => b (slotOf x)) :=
  average_piIcc_eq_average_paramBox (ι := ι) M
    (fun b : Slot ι (fun _ => 1) → ℤ => Φ (fun x => b (slotOf x)))

/-- **The direction identity**, in the form in which the regrouping consumes it: the level-`(n+1)`
coefficient of a slot, with the level-`(n+1)` parameters read on the `(·,0)` slots, is the sum of
the level-`n` coefficients over the parent. -/
theorem dir_step_eq_sum (D : IdxDatum) (d : ℕ) (c : ℤ) (n Λ : ℕ) (al : D.Idx (n + 1))
    (b : Slot (D.S (n + 1)) (fun _ => 1) → ℤ) (s : D.S (n + 2)) :
    (Λ : ℤ) * ((d : ℤ) - ((n + 1 : ℕ) : ℤ)) *
        D.dir d c (n + 1) (D.par (n + 1) s) (padUpdate D n al (fun x => b (slotOf x)))
      = ∑ s' ∈ (D.par (n + 1) s).1,
          pFlat D d c n (Λ * (d - (n + 1))) s' (encD D (n + 1) al) * b (slotOf s') := by
  have h := pFlat_splitUpd_eq_sum_slot D d c n Λ al (fun x => b (slotOf x)) s
  rw [show pFlat D d c (n + 1) Λ s (encD D (n + 2) (splitUpd D n al (fun x => b (slotOf x))))
        = (Λ : ℤ) * ((d : ℤ) - ((n + 1 : ℕ) : ℤ)) *
            D.dir d c (n + 1) (D.par (n + 1) s) (padUpdate D n al (fun x => b (slotOf x)))
        from by rw [pFlat_encD, pad_splitUpd]] at h
  exact h

/-- `SupportIn f N` gives the vanishing on the symmetric interval `symIcc N`. -/
theorem SupportIn.symIcc {f : ℤ → ℂ} {N : ℕ} (h : Work.Peluse.SupportIn f N) :
    ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → f x = 0 := by
  intro x hx
  refine h x ?_
  by_contra hcon
  push_neg at hcon
  exact hx (by
    rw [Work.Peluse.symIcc, Finset.mem_Icc]
    have h1 : (x.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hcon
    rw [Int.natCast_natAbs] at h1
    exact abs_le.mp h1)

end

end Work.Peluse.Prop36SW
