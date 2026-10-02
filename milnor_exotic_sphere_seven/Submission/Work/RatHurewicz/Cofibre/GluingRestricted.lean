import Mathlib
import Submission.Work.RatHurewicz.Cofibre.Gluing
import Submission.Work.RatHurewicz.AttachPush.PushOff

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The restricted-branch gluing lemma (the `ρ : cofibreU ι → E` case)

The cone branch is only defined on `↥T` (for `ρ` this is `coneBaseLtHalf : C(↥{h < 1/2}, E)`), so
the global-branch lemma `continuous_of_sumElim` does not apply.  Here the two clopen pieces

  `Uinl = {a | a.1 ∈ Sum.inl '' univ}`,  `Uinr = {a | a.1 ∈ Sum.inr '' T}`

of `↥(q ⁻¹' S)` are glued with `continuous_of_isOpen_cover`.

**Key Lean point** (this is the resolution of the earlier three failures): `rintro ⟨k, hk⟩` on
`a ∈ ⋃ k, U k` unfolds the *definition* of `Set.iUnion` — which is `sUnion`-shaped, so the witness
is a *set* `t ∈ Set.range U` and `cases k` fails.  The lemma `Set.mem_iUnion` states the standard
form, so **`rw [Set.mem_iUnion]` first**, and then the witness is indeed `k : Bool`.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {E F : Type} [TopologicalSpace E] [TopologicalSpace F]

/-- **Gluing lemma, restricted-branch case.** -/
theorem continuous_of_sumPiecewise [Nonempty E] [Nonempty F] (ι : C(F, E))
    {Z : Type} [TopologicalSpace Z]
    {T : Set (Work.Stems.Cone F)} (hT : IsOpen T) (f : C(E, Z)) (g : C(↥T, Z))
    {Φ : E ⊕ Work.Stems.Cone F → Z}
    (h1 : ∀ e, Φ (Sum.inl e) = f e)
    (h2 : ∀ (y : Work.Stems.Cone F) (hy : y ∈ T), Φ (Sum.inr y) = g ⟨y, hy⟩)
    {S : Set (cofibre ι)}
    (hS : (Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' S
      = Sum.inl '' (Set.univ : Set E) ∪ Sum.inr '' T) :
    Continuous fun a : ↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' S) => Φ a.1 := by
  classical
  obtain ⟨f₀⟩ : Nonempty F := inferInstance
  obtain ⟨e₀⟩ : Nonempty E := inferInstance
  let y₀ : Work.Stems.Cone F := Work.Stems.coneIncl f₀
  let Uinl : Set ↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' S) :=
    {a | a.1 ∈ Sum.inl '' (Set.univ : Set E)}
  let Uinr : Set ↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' S) :=
    {a | a.1 ∈ Sum.inr '' T}
  have hUinl : IsOpen Uinl := isOpen_sumInl_cofibre.preimage continuous_subtype_val
  have hUinr : IsOpen Uinr := (isOpen_sumInr_cofibre (E := E) hT).preimage continuous_subtype_val
  have hcov : Uinl ∪ Uinr = Set.univ := by
    ext a
    constructor
    · intro _; trivial
    · intro _
      have hmem : (a.1 : E ⊕ Work.Stems.Cone F) ∈
          Sum.inl '' (Set.univ : Set E) ∪ Sum.inr '' T := by
        rw [← hS]; exact a.2
      exact hmem
  let extL : ↥Uinl → E :=
    fun a => Sum.elim (fun e : E => e) (fun _ : Work.Stems.Cone F => e₀) a.1.1
  have hextL : Continuous extL :=
    (continuous_id.sumElim continuous_const).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  have hc1 : Continuous fun a : ↥Uinl => Φ a.1.1 := by
    refine (f.continuous.comp hextL).congr (fun a => ?_)
    show f (extL a) = Φ a.1.1
    rcases a.2 with ⟨e, -, he⟩
    have hval : a.1.1 = Sum.inl e := he.symm
    have h1a : extL a = e := by
      show Sum.elim (fun e : E => e) (fun _ : Work.Stems.Cone F => e₀) a.1.1 = e
      rw [hval]
      rfl
    rw [h1a, hval, h1 e]
  let extR : ↥Uinr → ↥T :=
    fun a => ⟨Sum.elim (fun _ : E => y₀) (fun y : Work.Stems.Cone F => y) a.1.1, by
      rcases a.2 with ⟨y, hy, hyeq⟩
      rw [← hyeq]
      simpa using hy⟩
  have hextR : Continuous extR :=
    Continuous.subtype_mk ((continuous_const.sumElim continuous_id).comp
      (continuous_subtype_val.comp continuous_subtype_val)) (fun a => (extR a).2)
  have hc2 : Continuous fun a : ↥Uinr => Φ a.1.1 := by
    refine (g.continuous.comp hextR).congr (fun a => ?_)
    show g (extR a) = Φ a.1.1
    rcases a.2 with ⟨y, hy, hyeq⟩
    have hval : a.1.1 = Sum.inr y := hyeq.symm
    have harg : extR a = (⟨y, hy⟩ : ↥T) := Subtype.ext (by
      show Sum.elim (fun _ : E => y₀) (fun y : Work.Stems.Cone F => y) a.1.1 = y
      rw [hval]
      rfl)
    rw [harg, hval, h2 y hy]
  let Ufam : Bool → Set ↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' S) :=
    fun k => if k then Uinr else Uinl
  have hUfam : ∀ k, IsOpen (Ufam k) := by
    intro k
    cases k
    · exact hUinl
    · exact hUinr
  have hcovfam : Set.iUnion Ufam = Set.univ := by
    rw [show Set.iUnion Ufam = Uinl ∪ Uinr from ?_, hcov]
    ext a
    rw [Set.mem_iUnion]
    constructor
    · rintro ⟨k, hk⟩
      cases k
      · exact Or.inl (by simpa [Ufam] using hk)
      · exact Or.inr (by simpa [Ufam] using hk)
    · rintro (h | h)
      · exact ⟨false, by simpa [Ufam] using h⟩
      · exact ⟨true, by simpa [Ufam] using h⟩
  have hgfam : ∀ k, Continuous fun x : ↥(Ufam k) => Φ x.1.1 := by
    intro k
    cases k
    · exact hc1
    · exact hc2
  exact continuous_of_isOpen_cover hUfam hcovfam hgfam

end

end Work.RatHurewicz
