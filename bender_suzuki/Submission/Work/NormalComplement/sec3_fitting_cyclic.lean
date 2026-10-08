/-
# Peterfalvi I Ch. III §3 Prop. 1: `F(E ∩ V)` is cyclic

Let `H` be strongly embedded in `G`, `t ∉ H` an involution, `W ⊴ H` with `H = W·D`,
`D = H ∩ H^t`, `E = W ∩ D` and `V = C_D(t) = centD H t`.  This file proves

* `sec3_fitting_cyclic` — the statement requested by area `NormalComplement`: if `2 ≤ |K|`
  (`K = J(D,t) = Kset D t`) and the Fitting subgroup `F = F(E ∩ V)` of `E ∩ V` acts
  fixed-point-freely on `K`, then `F` is **cyclic**.

This is the last line of the proof of Ch. III §3 Prop. 1 (p.177): "step 3 ⇒ `F(E ∩ V)` is cyclic
(odd Sylows acting fixed-point-freely on `K`, App. I (5)(c))"; the cyclicity of `F(E ∩ V)` is used
there to embed `(E ∩ V)/F(E ∩ V)` into the abelian group `Aut F(E ∩ V)`.

The mathematical content splits into two halves.

* **The Sylow half** (`isCyclic_of_fpf_invertedBy`, `isPGroup_isCyclic_of_le_fitEV`).  `|D|` is odd
  (`H` strongly embedded, `t ∉ H`), hence `D` is solvable (`hFT`), and `t` normalises `D` with
  `(|D|, 2) = 1`, so App. I (1)(b) (`appI_one`) identifies `K = J(D,t) = Kset D t` with the
  left-hand commutator set `Kapp t D`.  For a prime `p` and a `p`-subgroup `U ≤ D ∩ C_G(t)` acting
  fixed-point-freely on `K` with `2 ≤ |K|`, App. I (5)(c) (`appI_five_c_prime`) gives that `U` is
  cyclic; the Huppert input "an odd `p`-group acting fixed-point-freely is cyclic" is proved inside
  `appI_five_c_prime` (`fpf_pgroup_isCyclic`), after passing to a `U`-invariant Sylow `q`-subgroup
  `Q` of `⟨K⟩` and the nonzero quotient `N_Q(V ∩ Q)/(V ∩ Q)`.  Applied to `D = twoPoint H t` and
  `U ≤ F(E ∩ V) ≤ E ∩ V ≤ V = D ∩ C_G(t)`, this says that every `p`-subgroup of `F(E ∩ V)` is
  cyclic (`isPGroup_isCyclic_of_le_fitEV`).
* **The nilpotency half** (`isCyclic_fitEV`).  `F(E ∩ V)` is nilpotent (Fitting's theorem,
  `fitting_isNilpotent`), so by Mathlib's `IsZGroup` instance
  (`GroupTheory/SpecificGroups/ZGroup.lean`, line 127: a finite nilpotent group all of whose Sylow
  subgroups are cyclic is cyclic) it suffices to know that every Sylow subgroup of `F(E ∩ V)` is
  cyclic, which is the Sylow half transported from subgroups of `G` to subgroups of `F(E ∩ V)`
  along `P ≃ P.map F.subtype`.
-/
import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.appI_one
import Submission.Work.NormalComplement.appI_four
import Submission.Work.NormalComplement.appI_five_c_prime
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.fitting_isNilpotent
import Submission.Work.Fitting.fitting_eq_iSup_pCore

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

/-- **Peterfalvi I, Appendix I (5)(c) in the form in which `J(D,t)` is used**: if `D` has odd order,
`t` is an involution normalising `D` (so `(2, |D|) = 1`), and `U ≤ D ∩ C_G(t)` is a `p`-subgroup
acting fixed-point-freely on `K = J(D,t) = Kset D t` with `2 ≤ |K|`, then `U` is cyclic.

App. I (1)(b) identifies `Kset D t` with the commutator set `Kapp t D` (`appI_one`), and App. I
(5)(c) (`appI_five_c_prime`) then gives cyclicity, once the odd order group `D` is known solvable —
which is where `FeitThompsonProp` enters (the printed Appendix I assumes solvability of `D`). -/
theorem isCyclic_of_fpf_invertedBy (hFT : Submission.Blueprint.FeitThompsonProp)
    {G : Type} [Group G] [Finite G] {D : Subgroup G} (hDodd : Odd (Nat.card D)) {t : G}
    (ht : orderOf t = 2) (htD : NormalizedBy t D)
    {p : ℕ} (hp : p.Prime) {U : Subgroup G} (hUD : U ≤ D)
    (hUC : U ≤ Subgroup.centralizer ({t} : Set G)) (hUp : IsPGroup p U)
    (hK2 : 2 ≤ (Kset D t).ncard)
    (hfpf : ∀ u ∈ U, u ≠ 1 → ∀ k ∈ Kset D t, u * k * u⁻¹ = k → k = 1) :
    IsCyclic ↥U := by
  have hcop : (Nat.card ↥D).Coprime 2 := Nat.coprime_two_right.mpr hDodd
  have hsolv : Group.IsSolvable ↥D := hFT ↥D hDodd
  have hKapp : Kapp t D = Kset D t := (appI_one Nat.prime_two ht htD hcop).2 rfl |>.1
  have hU : U ≤ Subgroup.centralizer ({t} : Set G) ⊓ D := le_inf hUC hUD
  have hUodd : Odd (Nat.card ↥U) := Odd.of_dvd_nat hDodd (Subgroup.card_dvd_of_le hUD)
  have hfpf' : ∀ u ∈ U, u ≠ 1 → ∀ k ∈ Kapp t D, u * k * u⁻¹ = k → k = 1 := by
    intro u hu hu1 k hk hfix
    rw [hKapp] at hk
    exact hfpf u hu hu1 k hk hfix
  have hK2' : 2 ≤ (Kapp t D).ncard := by rw [hKapp]; exact hK2
  have hres := (appI_five_c_prime (G := G) (X := D) Nat.prime_two ht htD hcop hsolv hp hU hUp).2
  by_cases hUne : U = ⊥
  · rw [hUne]
    exact isCyclic_of_subsingleton
  · exact hres hUne hK2' hfpf' hUodd

namespace Sec3FittingCyclic

/-- `F(E ∩ V)`, the Fitting subgroup of `E ∩ V = (W ∩ D) ∩ V`, written in the ambient group `G`
(`V = centD H t = C_D(t)`).  This is the subgroup whose cyclicity `sec3_fitting_cyclic` asserts. -/
noncomputable abbrev fitEV {G : Type*} [Group G] (H : Subgroup G) (t : G) (W : Subgroup G) :
    Subgroup G :=
  Design.fitSub (Design.Egrp H t W ⊓ centD H t)

/-- For an involution `t`, `t` normalises the two-point stabiliser `D = H ∩ H^t = twoPoint H t`.
(`x ∈ t H t⁻¹` gives `x = t h t⁻¹` with `h ∈ H`, whence `t x t⁻¹ = h ∈ H`, and trivially
`t x t⁻¹ ∈ t H t⁻¹`.) -/
lemma normalizedBy_twoPoint_sec3 {G : Type*} [Group G] {H : Subgroup G} {t : G} (ht : orderOf t = 2) :
    NormalizedBy t (twoPoint H t) := by
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h
    simpa [pow_two] using h
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  intro x hx
  obtain ⟨hxH, hxHt⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨h, hh, hxh⟩ := Subgroup.mem_map.mp hxHt
  have hx_eq : x = t * h * t⁻¹ := by
    simpa [MulAut.conj_apply] using hxh.symm
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [hx_eq, hti]
    have key : t * (t * h * t) * t = h := by
      calc t * (t * h * t) * t = (t * t) * h * (t * t) := by group
        _ = h := by rw [ht2]; group
    rw [key]
    exact hh
  · refine Subgroup.mem_map.mpr ⟨x, hxH, ?_⟩
    simp [MulAut.conj_apply]

/-- The Fitting subgroup of a subgroup, mapped into the ambient group, is nilpotent: the Fitting
subgroup of a finite group is nilpotent (`fitting_isNilpotent`), and nilpotency transports along
the isomorphism `H ≃ H.map H.subtype`. -/
lemma isNilpotent_fitSub {G : Type*} [Group G] [Finite G] (X : Subgroup G) :
    Group.IsNilpotent ↥(Design.fitSub X) := by
  haveI := Work.Fitting.fitting_isNilpotent ↥X
  exact Group.nilpotent_of_mulEquiv
    (Subgroup.equivMapOfInjective (Work.Fitting.fitting ↥X) X.subtype X.subtype_injective)

/-- **Sylow half of §3 Prop. 1's last step.**  Under the hypotheses of `sec3_fitting_cyclic`,
every `p`-subgroup `U` of `F(E ∩ V)` is cyclic.

Indeed `U ≤ F(E ∩ V) ≤ E ∩ V ≤ V = D ∩ C_G(t)` with `D = twoPoint H t`; `|D|` is odd (from
`IsStronglyEmbedded H` and `t ∉ H`), `t` normalises `D` (it is an involution), `|U|` is odd (as
`U ≤ D`), and `U` acts fixed-point-freely on `K = J(D,t)`; so `isCyclic_of_fpf_invertedBy`
(App. I (1)(b) plus (5)(c), with `D` solvable by `hFT`) applies. -/
lemma isPGroup_isCyclic_of_le_fitEV {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G}
    (hFT : FeitThompsonProp) (h : Design.Setup3 G H t W)
    (hK2 : 2 ≤ (Kset (twoPoint H t) t).ncard)
    (hfpf : Design.FpfOn (fitEV H t W) (Kset (twoPoint H t) t))
    {p : ℕ} (hp : p.Prime) {U : Subgroup G} (hU : U ≤ fitEV H t W) (hUp : IsPGroup p U) :
    IsCyclic ↥U := by
  have ht : orderOf t = 2 := h.invol
  have hoddD : Odd (Nat.card ↥(twoPoint H t)) := h.se.2.2 t h.notMem
  have htD : NormalizedBy t (twoPoint H t) := normalizedBy_twoPoint_sec3 ht
  have hfit : fitEV H t W ≤ Design.Egrp H t W ⊓ centD H t :=
    Subgroup.map_subtype_le (Work.Fitting.fitting ↥(Design.Egrp H t W ⊓ centD H t))
  have hle : fitEV H t W ≤ Subgroup.centralizer ({t} : Set G) ⊓ twoPoint H t := by
    refine hfit.trans (le_inf ?_ ?_)
    · exact fun x hx => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).2).2
    · exact fun x hx => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).2).1
  exact isCyclic_of_fpf_invertedBy hFT hoddD ht htD hp (hU.trans (hle.trans inf_le_right))
    (hU.trans (hle.trans inf_le_left)) hUp hK2
    (fun u hu hu1 k hk hfix => hfpf u (hU hu) hu1 k hk hfix)

/-- **§3 Prop. 1, last step**: `F(E ∩ V)` is cyclic, given that `F(E ∩ V)` acts
fixed-point-freely on `K = J(D,t)` and `2 ≤ |K|`.

`F = F(E ∩ V)` is nilpotent (`isNilpotent_fitSub`), and its Sylow `p`-subgroups are `p`-subgroups
of `G` contained in `F`, hence cyclic by `isPGroup_isCyclic_of_le_fitEV`; so `IsZGroup ↥F` holds,
and Mathlib's instance "finite nilpotent Z-group ⟹ cyclic" finishes. -/
lemma isCyclic_fitEV {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G}
    (hFT : FeitThompsonProp) (h : Design.Setup3 G H t W)
    (hK2 : 2 ≤ (Kset (twoPoint H t) t).ncard)
    (hfpf : Design.FpfOn (fitEV H t W) (Kset (twoPoint H t) t)) :
    IsCyclic ↥(fitEV H t W) := by
  haveI hnil : Group.IsNilpotent ↥(fitEV H t W) :=
    isNilpotent_fitSub (Design.Egrp H t W ⊓ centD H t)
  haveI hZ : IsZGroup ↥(fitEV H t W) := ⟨fun p hp P => by
    have hP : IsPGroup p ↥(Subgroup.map (fitEV H t W).subtype (P : Subgroup ↥(fitEV H t W))) :=
      IsPGroup.map P.isPGroup' (fitEV H t W).subtype
    have hcyc : IsCyclic ↥(Subgroup.map (fitEV H t W).subtype
        (P : Subgroup ↥(fitEV H t W))) :=
      isPGroup_isCyclic_of_le_fitEV hFT h hK2 hfpf hp (Subgroup.map_subtype_le _) hP
    exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective (P : Subgroup ↥(fitEV H t W))
      (fitEV H t W).subtype (fitEV H t W).subtype_injective)).mpr hcyc⟩
  exact inferInstance

end Sec3FittingCyclic

theorem sec3_fitting_cyclic (hFT : Submission.Blueprint.FeitThompsonProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G}
    (h : Work.NormalComplement.Design.Setup3 G H t W)
    (hK2 : 2 ≤ (Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t).ncard)
    (hFpf : Work.NormalComplement.Design.FpfOn
      (Work.NormalComplement.Design.fitSub
        (Work.NormalComplement.Design.Egrp H t W ⊓ Submission.Blueprint.centD H t))
      (Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t)) :
    IsCyclic ↥(Work.NormalComplement.Design.fitSub
      (Work.NormalComplement.Design.Egrp H t W ⊓ Submission.Blueprint.centD H t)) :=
  Sec3FittingCyclic.isCyclic_fitEV hFT h hK2 hFpf

end Work.NormalComplement
