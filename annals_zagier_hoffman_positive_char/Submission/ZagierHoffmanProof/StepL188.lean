import Submission.ZagierHoffmanProof.StepL187
import Submission.ZagierHoffmanProof.StepL168
import Submission.ZagierHoffmanProof.StepL2

set_option autoImplicit false
set_option maxHeartbeats 40000000
open Polynomial RatFunc
open scoped BigOperators
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Step L188: THE `domLevel = 1` CORNER — the `(q)` R1 leaf and the head-`≤ q` reduction

The recursion's case (b) sends a `¬(k−1)`-admissible member `m` to the ambient chain port at
`k' := domLevel m`.  When `k' ≥ 2` the four committed ports apply directly; the present module
treats `k' = 1`, i.e. the members whose OWN in-domain level is 1:

  • `domLevel q m = 1` splits as `(initLen q m = 0)` — the visible head exceeds `q`
    (`pad0 m 0 > q`) — or `(depth m = 1 ∧ initLen q m = 1)` — the tuple is a SINGLETON
    `single c` with `c ≤ q`;
  • in the singleton case with `c ≠ q` the tuple is `Λ`-admissible for EVERY `Λ ≥ 1`
    (`kAdm_single_of_ne_q`), so the port's own `admExpT_self` dispatch covers it — no corner;
  • the genuine corner is therefore the R1 leaf `m = single (qExp F)`, and
    ★★ `maink_r1_leaf` expands it at EVERY level `Λ ≥ 1`: the committed R1 relation
    `zeta_R1` writes `ζ_A(q) = −D1rat · ζ_A(1, q−1)`, the single output `(1, q−1)` is
    `Λ`-admissible (`kAdm_pair_one_general`, for all `Λ ≥ 1`, since its last entry is `q−1 ≠ q`)
    with weight `q = w`, and `pair_one_qminus_order` gives the prefix order at every `ℓ ≥ 1`;
  • ★ `maink_domLevel_one_of_head_le`: for a member with `pad0 m 0 ≤ q` the corner therefore
    produces an expansion at every level — the chains' members have heads `≤ q` by the
    `hhead`/`hbhd`/`hc0` fields of `maink_config_full` (and `hbhd` literally: heads `= 1`),
    so the corner is discharged for them.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ `(1, q−1)` is `Λ`-admissible for every `Λ ≥ 1` (its last entry is `q−1 ≠ q`). -/
lemma kAdm_pair_one_general (Λ : ℕ) (hΛ : 1 ≤ Λ) :
    kAdmissible (Nat.card F) (pair oneExp (qMinusExp F)) Λ := by
  classical
  constructor
  · intro x hx
    by_cases hx2 : x < 2
    · rcases Nat.eq_zero_or_pos x with hx0 | hxpos
      · subst hx0
        rw [pad0_of_lt (pair oneExp (qMinusExp F)) (by omega : 0 < 2), pair_zero]
        change (1 : ℕ) ≤ Nat.card F
        have h2 : 2 ≤ Nat.card F := card_ge_two F
        omega
      · have hx1 : x = 1 := by omega
        subst hx1
        rw [pad0_of_lt (pair oneExp (qMinusExp F)) (by omega : 1 < 2), pair_one]
        change (qMinusExp F : ℕ) ≤ Nat.card F
        rw [show (qMinusExp F : ℕ) = Nat.card F - 1 by rfl]
        exact Nat.sub_le _ _
    · have hzero : pad0 (pair oneExp (qMinusExp F)) x = 0 :=
        pad0_of_ge (pair oneExp (qMinusExp F)) (by omega)
      rw [hzero]
      exact Nat.zero_le _
  · rintro ⟨hr1, hrk, hall, hlast⟩
    -- the tuple has depth `2`, so the form forces its last entry `q−1` to be `q`
    have hlast' : (qMinusExp F : ℕ) = Nat.card F := by
      have hidx2 : (⟨2 - 1, by omega⟩ : Fin 2) = ⟨1, by omega⟩ := Fin.ext (by rfl)
      have hval : ((pair oneExp (qMinusExp F)) ⟨2 - 1, by omega⟩ : ℕ) = (qMinusExp F : ℕ) := by
        rw [hidx2]
        exact congrArg (fun t : ℕ+ => (t : ℕ)) (pair_one oneExp (qMinusExp F))
      rw [hval] at hlast
      exact hlast
    have hq : (qMinusExp F : ℕ) = Nat.card F - 1 := rfl
    have h2 : 2 ≤ Nat.card F := card_ge_two F
    omega

/-- ★★ THE R1 LEAF: `single (qExp F)` expands at EVERY level `Λ ≥ 1`. -/
theorem maink_r1_leaf (w : ℕ) (hw : weight 1 (single (qExp F)) = w) (Λ : ℕ) (hΛ : 1 ≤ Λ) :
    AdmExpT F w Λ (single (qExp F)) := by
  classical
  have hout : kAdmissible (Nat.card F) (pair oneExp (qMinusExp F)) Λ :=
    kAdm_pair_one_general F Λ hΛ
  have houtw : weight 2 (pair oneExp (qMinusExp F)) = w := by
    rw [weight_pair]
    rw [show (oneExp : ℕ) = 1 by rfl]
    rw [show (qMinusExp F : ℕ) = Nat.card F - 1 by rfl]
    have h2 : 2 ≤ Nat.card F := card_ge_two F
    have hwq : w = Nat.card F := by
      rw [← hw, weight_single]
      rfl
    omega
  have hid : ζ_A F (single (qExp F)) =
      ∑ _p : Fin 1, (((-D1rat F : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (pair oneExp (qMinusExp F))) := by
    rw [Fin.sum_univ_one]
    have hcast : (((-D1rat F : RatFunc F)) : RatFunc.CompletionAtInfty F) =
        -(D1rat F : RatFunc.CompletionAtInfty F) := by
      change (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (-D1rat F)) =
        -(algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (D1rat F))
      rw [map_neg]
    have hd : (D1rat F : RatFunc.CompletionAtInfty F) = D1c F := D1c_eq_D1rat F
    calc ζ_A F (single (qExp F))
        = -(D1c F * ζ_A F (pair oneExp (qMinusExp F))) :=
          eq_neg_of_add_eq_zero_left (zeta_R1 F)
      _ = ((-D1rat F : RatFunc F) : RatFunc.CompletionAtInfty F) *
            ζ_A F (pair oneExp (qMinusExp F)) := by
          rw [hcast, hd]
          ring
  have horder : ∀ _p : Fin 1, ∀ ℓ : ℕ, Λ ≤ ℓ →
      psum (pair oneExp (qMinusExp F)) ℓ ≤ psum (single (qExp F)) ℓ := by
    intro _p ℓ hℓ
    exact pair_one_qminus_order F ℓ (by omega)
  have e : ∀ _p : Fin 1, AdmExpT F w Λ (pair oneExp (qMinusExp F)) := by
    intro _p
    exact admExpT_self F w Λ (by omega) (pair oneExp (qMinusExp F)) houtw hout
  exact admExpT_combine F w Λ (single (qExp F))
    (fun _ : Fin 1 => 2) (fun _ => by omega)
    (fun _ : Fin 1 => pair oneExp (qMinusExp F)) (fun _ : Fin 1 => -D1rat F) hid horder e

/-- ★ THE `domLevel = 1` CORNER FOR A MEMBER WITH HEAD `≤ q`: the member is either the R1 leaf
`(q)` — expanded by `maink_r1_leaf` — or a singleton `single c` with `c ≠ q`, which is
`Λ`-admissible for every `Λ ≥ 1` (hence already handled by the port's `admExpT_self`). -/
theorem maink_domLevel_one_of_head_le (w : ℕ) {r : ℕ} (m : Fin r → ℕ+)
    (hmw : weight r m = w) (hd : domLevel (Nat.card F) m = 1) (hhead : pad0 m 0 ≤ Nat.card F)
    (Λ : ℕ) (hΛ : 1 ≤ Λ) : AdmExpT F w Λ m ∨ kAdmissible (Nat.card F) m Λ := by
  classical
  by_cases hinit : initLen (Nat.card F) m < r
  · -- `initLen = 0`: the visible head exceeds `q`, contradicting `hhead`
    have hd' : initLen (Nat.card F) m + 1 = 1 := by
      rw [domLevel_eq_succ (Nat.card F) m hinit] at hd
      exact hd
    have hzero : initLen (Nat.card F) m = 0 := by omega
    have hfl : pad0 m 0 > Nat.card F := by
      have hgt := initLen_entry_gt (Nat.card F) m hinit
      have hpad0 : (m ⟨initLen (Nat.card F) m, hinit⟩ : ℕ) = (m ⟨0, by omega⟩ : ℕ) :=
        congrArg (fun t : ℕ+ => (t : ℕ)) (congrArg m (Fin.ext hzero))
      rw [pad0_of_lt m (by omega : 0 < r), ← hpad0]
      exact hgt
    omega
  · -- `initLen = r` and `r = 1`: `m` is a singleton
    have hd' : r = 1 := by
      rw [domLevel_eq_depth (Nat.card F) m (by omega)] at hd
      exact hd
    subst hd'
    have hentry : (m ⟨0, by omega⟩ : ℕ) = pad0 m 0 := (pad0_of_lt m (by omega)).symm
    by_cases hq : pad0 m 0 = Nat.card F
    · -- the R1 leaf
      left
      have hm_eq : m = single (qExp F) := by
        funext i
        apply Subtype.ext
        have h1 : (m ⟨0, by omega⟩ : ℕ) = Nat.card F := by
          rw [hentry, hq]
        have hi : i = ⟨0, by omega⟩ := Fin.ext (by omega)
        rw [hi]
        show (m ⟨0, by omega⟩ : ℕ) = (single (qExp F) ⟨0, by omega⟩ : ℕ)
        rw [h1]
        rfl
      rw [hm_eq] at hmw ⊢
      exact maink_r1_leaf F w hmw Λ hΛ
    · -- a singleton with entry `≠ q` is `Λ`-admissible
      right
      refine ⟨fun x hx => ?_, ?_⟩
      · by_cases hx0 : x = 0
        · subst hx0
          exact hhead
        · have hge : 1 ≤ x := by omega
          rw [pad0_of_ge m hge]
          exact Nat.zero_le _
      · rintro ⟨hr1, hrk, hall, hlast⟩
        have hidx : (⟨1 - 1, by omega⟩ : Fin 1) = ⟨0, by omega⟩ := Fin.ext (by rfl)
        have hlast' : (m ⟨0, by omega⟩ : ℕ) = Nat.card F := by
          have h := hlast
          rw [show (m ⟨1 - 1, by omega⟩ : ℕ) = (m ⟨0, by omega⟩ : ℕ) from
            congrArg (fun i => (m i : ℕ)) hidx] at h
          exact h
        exact hq (by rw [← hentry]; exact hlast')


/-- ★★ THE `domLevel = 1` CORNER, ASSEMBLED: for a weight-`w` member with `domLevel m = 1` and
head `≤ q` — the only case that arises for the chains' members (the `b`-heads are literally `1`
by `hbhd`, the `a`-members inherit the input's first entry which is `≤ q`) — there is an
expansion at EVERY level `Λ ≥ 1`. -/
theorem maink_domLevel_one_corner (w : ℕ) {r : ℕ} (m : Fin r → ℕ+)
    (hmw : weight r m = w) (hd : domLevel (Nat.card F) m = 1) (hhead : pad0 m 0 ≤ Nat.card F)
    (hinit : initLen (Nat.card F) m < r)
    (Λ : ℕ) (hΛ : 1 ≤ Λ) : AdmExpT F w Λ m := by
  rcases maink_domLevel_one_of_head_le F w m hmw hd hhead Λ hΛ with h | hadm
  · exact h
  · have hr : 0 < r := by have := domLevel_le_depth (Nat.card F) m hinit; omega
    exact admExpT_self F w Λ hr m hmw hadm

end ZagierHoffmanPositiveChar
