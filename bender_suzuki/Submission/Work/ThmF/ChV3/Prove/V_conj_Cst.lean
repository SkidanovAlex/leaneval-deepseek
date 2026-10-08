import Mathlib
import Submission.Work.ThmF.Prove.centDLowerCentralizerS
import Submission.Work.ThmF.ChV3.Prove.A_le_cst
import Submission.Work.ThmF.ChV3.Step16Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `V_conj_Cst`: `V = C_D(t)` normalises `C_G(st)`

Peterfalvi II, Ch. V §3, step (16)/(17) (the `C_G(st)` analogue of `V_conj_X5`).

Let `v ∈ V = centD H t = C_D(t)`.  By Peterfalvi II Ch. V §2 Lemma 3 a)
(`Work.ThmF.Prove.centDLowerCentralizerS`) `V` centralises the distinguished involution
`s ∈ Q` of the structure identity `t s t = r⁻¹ t r`; and by definition `V` centralises `t`.
Hence `v` centralises `s t`, so conjugation by `v` fixes `s t` and therefore maps the
centraliser of `{s t}` — that is, `C_G(st) = Cst s t` — onto itself.
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs

namespace Work.ThmF.ChV3.Prove

/-- If `v` centralises every element of a set `S`, then conjugation by `v` preserves the
centraliser of `S`. -/
theorem map_conj_centralizer_eq {G : Type} [Group G] {S : Set G} {v : G}
    (hv : ∀ x ∈ S, v * x = x * v) :
    (Subgroup.centralizer S).map (MulAut.conj v).toMonoidHom = Subgroup.centralizer S := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩ w hw
    have hxc : w * x = x * w := hx w hw
    show w * ((MulAut.conj v).toMonoidHom x) = (MulAut.conj v).toMonoidHom x * w
    rw [show (MulAut.conj v).toMonoidHom x = v * x * v⁻¹ from MulAut.conj_apply v x]
    have hvw : v * w = w * v := hv w hw
    have hv' : v⁻¹ * w = w * v⁻¹ := by
      calc v⁻¹ * w = v⁻¹ * (w * v) * v⁻¹ := by group
        _ = v⁻¹ * (v * w) * v⁻¹ := by rw [← hvw]
        _ = w * v⁻¹ := by group
    calc w * (v * x * v⁻¹) = (w * v) * x * v⁻¹ := by group
      _ = (v * w) * x * v⁻¹ := by rw [hvw]
      _ = v * (w * x) * v⁻¹ := by group
      _ = v * (x * w) * v⁻¹ := by rw [hxc]
      _ = (v * x) * (w * v⁻¹) := by group
      _ = (v * x) * (v⁻¹ * w) := by rw [hv']
      _ = (v * x * v⁻¹) * w := by group
  · intro y hy
    refine ⟨v⁻¹ * y * v, ?_, ?_⟩
    · intro w hw
      have hyc : w * y = y * w := hy w hw
      have hvw : v * w = w * v := hv w hw
      have hv' : v⁻¹ * w = w * v⁻¹ := by
        calc v⁻¹ * w = v⁻¹ * (w * v) * v⁻¹ := by group
          _ = v⁻¹ * (v * w) * v⁻¹ := by rw [← hvw]
          _ = w * v⁻¹ := by group
      calc w * (v⁻¹ * y * v) = (w * v⁻¹) * y * v := by group
        _ = (v⁻¹ * w) * y * v := by rw [← hv']
        _ = v⁻¹ * (w * y) * v := by group
        _ = v⁻¹ * (y * w) * v := by rw [hyc]
        _ = v⁻¹ * y * (w * v) := by group
        _ = v⁻¹ * y * (v * w) := by rw [← hvw]
        _ = (v⁻¹ * y * v) * w := by group
    · show (MulAut.conj v).toMonoidHom (v⁻¹ * y * v) = y
      rw [show (MulAut.conj v).toMonoidHom (v⁻¹ * y * v) = v * (v⁻¹ * y * v) * v⁻¹
        from MulAut.conj_apply v _]
      group

theorem V_conj_Cst {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hs : s ∈ Q) (hs2 : orderOf s = 2)
    (hr : r ∈ Q) (hsid : t * s * t = r⁻¹ * t * r) :
    ∀ v ∈ Submission.Blueprint.centD H t,
      Work.ThmF.ChV3.cj v (Work.ThmF.ChV3.Cst s t) = Work.ThmF.ChV3.Cst s t := by
  intro v hv
  -- `v ∈ V ≤ C_G(s)` (Peterfalvi II Ch. V §2 Lemma 3 a)).
  have hvs : v ∈ Subgroup.centralizer ({s} : Set G) :=
    Work.ThmF.Prove.centDLowerCentralizerS h hs hs2 hr hsid hv
  -- `v ∈ V ≤ C_G(t)` by definition of `V = C_D(t)`.
  have hvt : v ∈ Subgroup.centralizer ({t} : Set G) := (Subgroup.mem_inf.mp hv).2
  -- hence `v` centralises `s * t`.
  have hvst : v ∈ Work.ThmF.ChV3.Cst s t := by
    rw [Work.ThmF.ChV3.Cst]
    exact centralizer_mul_le_centralizer s t (Subgroup.mem_inf.mpr ⟨hvs, hvt⟩)
  have hcomm : v * (s * t) = (s * t) * v := by
    rw [Work.ThmF.ChV3.Cst] at hvst
    exact Subgroup.mem_centralizer_singleton_iff.mp hvst
  -- so conjugation by `v` fixes `{s * t}` and preserves its centraliser.
  have hmap : (Subgroup.centralizer ({s * t} : Set G)).map (MulAut.conj v).toMonoidHom
      = Subgroup.centralizer ({s * t} : Set G) :=
    map_conj_centralizer_eq (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hcomm)
  simpa [Work.ThmF.ChV3.cj, Work.ThmF.ChV3.Cst] using hmap

end Work.ThmF.ChV3.Prove
