/-
# Ch. III §4 Prop. 2 (b): `E'` is nilpotent, Hall in `G`, and has the primes of `|K|`

This module proves `Work.NormalComplement.NC4.prop2b`, Peterfalvi I Ch. III §4 Proposition 2 (b)
(p. 181), from the intermediate conclusions of the two preceding steps (`NC4/Defs.lean`):

* `Lemma1dConc` (Lemma 1 (d)): `P` is a `p`-Sylow of `D = H ⊓ H^t`, `E = E' ⋊ P`
  (`E' ⊓ P = ⊥`, `E' ⊔ P = E`);
* `Prop1Conc` (Prop. 1): the primes of `C = C_A(P)` are the primes `r ≠ p` of `|D|` with
  `r ∤ |K|`, they do not divide `|D : C|`, `⟨K⟩ ⊓ V ≤ [A,P]`, and `N = (⟨K⟩ ⊔ [A,P]) ⊔ P` is a
  normal complement of `C` in `D`;
* `Prop2aConc` (Prop. 2 (a)): `E = (⟨K⟩ ⊔ [A,P]) ⊔ P`, `E' = ⟨K⟩ ⊔ [A,P]`, `E' ⊓ V = [A,P]`.

Notation: `D = twoPoint H t`, `E = Egrp H t W = W ⊓ D`, `E' = Ecomm H t W = ⁅E,E⁆`,
`V = centD H t = C_D(t)`, `C = C_A(P) = A ⊓ C_G(P)`, `K = Kset D t`.

Route (the source's, with the details supplied):

* **`C_{E'}(P) = 1`.**  `Prop2aConc` gives `E = N`, so `C ⊓ E = C ⊓ N = ⊥` by `Prop1Conc`; and
  `E' ⊓ P = ⊥` by `Lemma1dConc`.  If `x ∈ E'` centralises `P` then `x ∈ D ⊓ N_G(P) = C ⊔ P`
  (`sec4_one_c`), say `x = c·q` with `c ∈ C`, `q ∈ P`; then `c = x·q⁻¹ ∈ E`, so `c ∈ C ⊓ E = ⊥`,
  and `x = q ∈ E' ⊓ P = ⊥`.
* **Nilpotency.**  `E' ≤ D` has odd order, so it is solvable (`hFT`); conjugation by an element of
  `P` is thus a fixed-point-free automorphism of `E'` of prime order `p`
  (`prop2b_aux_nilpotent`, i.e. Thompson's theorem in the solvable case,
  `Work.Frobenius.Fpf.isNilpotent_of_fpf_prime`).
* **The primes of `|E'|` are those of `|K|`** (`prop2b_aux_counts` for the cardinalities).
  `|D| = |E'|·p·|C|` and `|D : C| = |E'|·p`, so a prime `r | |E'|` is neither `p` (as `p ∤ |E'|`)
  nor a prime of `C`; if also `r ∤ |K|` then `r ∈ π` (`piSec4`) and `Prop1Conc` would give
  `r ∤ |D : C|`, a contradiction.  Conversely `|K|·|A| = |E'|·|C|`, so `r | |K|` dividing `|E'|·|C|`
  with `r ∤ |E'|` would force `r | |C|`, hence `r ∈ π`, hence `r ∤ |K|`.
* **Hall in `G`.**  If `r | |E'|` then `r | |K|`, and Ch. II §4 Prop. 2 (d) (`sec4_P2d`) gives an
  `r`-Sylow `R ≤ D` of `G`, so `r ∤ |G : D|`; and `|D : E'| = p·|C|` with `r ∤ p` and `r ∤ |C|`
  (else `r ∈ π` and `r ∤ |K|`).  Hence `r ∤ |G : E'| = |G:D|·|D:E'|`.
-/
import Mathlib
import Submission.Work.NormalComplement.NC4.Defs
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.sec4_P2d
import Submission.Work.NormalComplement.sec4_one_c
import Submission.Work.NormalComplement.NC4.prop2b_aux_counts
import Submission.Work.NormalComplement.NC4.prop2b_aux_nilpotent
import Submission.Work.Frobenius.Fpf.isNilpotent_of_fpf_prime

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement.NC4

theorem prop2b (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G}
    (h : Work.NormalComplement.Design.Setup45A G H t W p P A)
    (h1d : Work.NormalComplement.NC4.Lemma1dConc H t W p P A)
    (hP1 : Work.NormalComplement.NC4.Prop1Conc H t W p P A)
    (h2a : Work.NormalComplement.NC4.Prop2aConc H t W p P A) :
    Work.NormalComplement.NC4.Prop2bConc H t W p P A := by
  have hp : p.Prime := h.prime
  -- ## the counting identities of §4 Prop. 1, 2 (a)
  obtain ⟨h1c, h2c, h3c, h4c, h5c, h6c⟩ := prop2b_aux_counts h h1d hP1 h2a
  -- ## abbreviations
  set D : Subgroup G := twoPoint H t
  set E : Subgroup G := Work.NormalComplement.Design.Egrp H t W
  set E' : Subgroup G := Work.NormalComplement.Design.Ecomm H t W
  set V : Subgroup G := centD H t
  set C : Subgroup G := A ⊓ Subgroup.centralizer (P : Set G)
  set N : Subgroup G := (Work.NormalComplement.Kgrp (twoPoint H t) t ⊔
      Work.NormalComplement.Design.commSub A P) ⊔ P
  -- ## Lemma 1 (d) and Prop. 2 (a)
  have hE'_inf_P : E' ⊓ P = ⊥ := h1d.2.1
  have hE'_sup_P : E' ⊔ P = E := h1d.2.2
  have hE_eq_N : E = N := h2a.1
  -- ## Proposition 1
  have hpi1 : ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥C →
      Work.NormalComplement.Design.piSec4 H t p r := hP1.1
  have hpi2 : ∀ r : ℕ, Work.NormalComplement.Design.piSec4 H t p r →
      ¬ r ∣ C.relIndex D := hP1.2.1
  have hN_le_D : N ≤ D := hP1.2.2.2.1
  have hN_inf_C : N ⊓ C = ⊥ := hP1.2.2.2.2.2.1
  -- ## elementary consequences
  have hE_le_D : E ≤ D := inf_le_right
  have hE'_le_E : E' ≤ E := (Subgroup.commutator_le_sup E E).trans (le_of_eq (sup_idem E))
  have hE'_le_D : E' ≤ D := hE'_le_E.trans hE_le_D
  have hE'_norm : E ≤ Subgroup.normalizer (E' : Set G) :=
    Subgroup.normalizer_commutator_ge_left E E
  have hP_le_E : P ≤ E := hE'_sup_P ▸ le_sup_right
  have hP_le_V : P ≤ V := le_trans h.P_le inf_le_right
  have hA_le_V : A ≤ V := h.A_le
  have hV_le_D : V ≤ D := inf_le_left
  have hC_le_A : C ≤ A := inf_le_left
  have hC_le_centP : C ≤ Subgroup.centralizer (P : Set G) := inf_le_right
  have hC_le_V : C ≤ V := hC_le_A.trans hA_le_V
  have hC_comm : ∀ c ∈ C, ∀ q ∈ P, c * q = q * c :=
    fun c hc q hq => (Subgroup.mem_centralizer_iff.mp (hC_le_centP hc) q hq).symm
  have hP_norm_C : P ≤ Subgroup.normalizer (C : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro q hq c hc
    have h1 : q * c * q⁻¹ = c := by rw [← hC_comm c hc q hq]; group
    rw [h1]; exact hc
  have hP_norm_E' : P ≤ Subgroup.normalizer (E' : Set G) := hP_le_E.trans hE'_norm
  have hCE : C ⊓ E = ⊥ := by
    rw [hE_eq_N, inf_comm]
    exact hN_inf_C
  -- ## `C_{E'}(P) = 1`
  have hcent : ∀ x ∈ E', (∀ q ∈ P, x * q = q * x) → x = 1 := by
    intro x hxE' hxc
    have hxD : x ∈ D := hE'_le_D hxE'
    have hxN : x ∈ Subgroup.normalizer (P : Set G) :=
      Subgroup.centralizer_le_normalizer (P : Set G)
        (Subgroup.mem_centralizer_iff.mpr (fun y hy => (hxc y hy).symm))
    have hCP : D ⊓ Subgroup.normalizer (P : Set G) = C ⊔ P :=
      (Work.NormalComplement.sec4_one_c hFT h).1
    have hxCP : x ∈ C ⊔ P := by
      rw [← hCP]
      exact Subgroup.mem_inf.mpr ⟨hxD, hxN⟩
    obtain ⟨c, hcC, q, hqP, hxq⟩ := (Work.NormalComplement.mem_sup_mul hP_norm_C).mp hxCP
    have hcE : c ∈ E := by
      have h1 : c = x * q⁻¹ := by rw [hxq]; group
      rw [h1]
      exact E.mul_mem (hE'_le_E hxE') (E.inv_mem (hP_le_E hqP))
    have hc1 : c = 1 := by
      have h1 : c ∈ C ⊓ E := Subgroup.mem_inf.mpr ⟨hcC, hcE⟩
      rw [hCE] at h1
      exact Subgroup.mem_bot.mp h1
    have hxP : x ∈ P := by
      have h1 : x = q := by rw [hxq, hc1, one_mul]
      rw [h1]; exact hqP
    have h1 : x ∈ E' ⊓ P := Subgroup.mem_inf.mpr ⟨hxE', hxP⟩
    rw [hE'_inf_P] at h1
    exact Subgroup.mem_bot.mp h1
  -- ## nilpotency
  have hodd_E' : Odd (Nat.card ↥E') :=
    Work.ThreePoints.Odd.of_dvd (Subgroup.card_dvd_of_le hE'_le_D) (h.se.2.2 t h.notMem)
  have hsolv : Group.IsSolvable ↥E' := hFT ↥E' hodd_E'
  have hnilp : Group.IsNilpotent ↥E' :=
    prop2b_aux_nilpotent hp h.P_card hP_norm_E' hcent hsolv
  -- ## the prime divisors of `|E'|` are those of `|K|`
  have hprimes : ∀ r : ℕ, r.Prime →
      (r ∣ Nat.card ↥E' ↔ r ∣ (Work.NormalComplement.Kset (twoPoint H t) t).ncard) := by
    intro r hr
    constructor
    · intro hrdvd
      by_contra hnot
      have hDdvd : r ∣ Nat.card ↥D := dvd_trans hrdvd (Subgroup.card_dvd_of_le hE'_le_D)
      have hrp : r ≠ p := fun hrp => h2c (hrp ▸ hrdvd)
      have hpi : Work.NormalComplement.Design.piSec4 H t p r := ⟨hr, hDdvd, hrp, hnot⟩
      have h2 := hpi2 r hpi
      rw [h5c] at h2
      exact h2 (dvd_mul_of_dvd_left hrdvd p)
    · intro hrdvdK
      by_contra hnot
      have h1 : r ∣ Nat.card ↥E' * Nat.card ↥C := by
        rw [← h6c]
        exact dvd_mul_of_dvd_left hrdvdK (Nat.card ↥A)
      rcases hr.dvd_mul.mp h1 with h | h
      · exact hnot h
      · exact (hpi1 r hr h).2.2.2 hrdvdK
  -- ## `E'` is a Hall subgroup of `G`
  have hhall : Nat.Coprime (Nat.card ↥E') E'.index := by
    by_contra hbad
    obtain ⟨r, hr, hrdvd, hrindex⟩ := Nat.Prime.not_coprime_iff_dvd.mp hbad
    have hrK : r ∣ (Work.NormalComplement.Kset (twoPoint H t) t).ncard := (hprimes r hr).mp hrdvd
    obtain ⟨R, hRD, hRp, hRidx⟩ :=
      Work.NormalComplement.sec4_P2d hC4 h.sit h.se h.invol h.notMem r hr hrK
    have hrD : ¬ r ∣ D.index := by
      intro hdiv
      have h1 : R.index = R.relIndex D * D.index := (Subgroup.relIndex_mul_index hRD).symm
      rw [h1] at hRidx
      exact hRidx (dvd_mul_of_dvd_right hdiv _)
    have hrE' : ¬ r ∣ E'.relIndex D := by
      rw [h4c]
      refine hr.not_dvd_mul ?_ ?_
      · intro hdiv
        have hr1 : r = p := by
          rcases (Nat.dvd_prime hp).mp hdiv with h | h
          · exact absurd h (by have := hr.two_le; omega)
          · exact h
        exact h2c (hr1 ▸ hrdvd)
      · intro hdiv
        exact (hpi1 r hr hdiv).2.2.2 hrK
    have h1 : E'.index = E'.relIndex D * D.index := (Subgroup.relIndex_mul_index hE'_le_D).symm
    exact hr.not_dvd_mul hrE' hrD (h1 ▸ hrindex)
  exact ⟨hnilp, hhall, hprimes⟩

end Work.NormalComplement.NC4
