import Submission.Work.ZassenhausSuzuki.canon_relations
import Submission.Work.ZassenhausSuzuki.szTildeAux
import Submission.Work.ZassenhausSuzuki.hG_tilde_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- **H4** (`NOTES_LEAD_bs_zs_tits.md` §3, design leaf `TitsDesign.f_tilde`): `f(∼x) = h(x)·x·h(x)⁻¹`.
Proved here directly from `tildeOf_eq` (`∼x = d·f(x)·d⁻¹` with `d = (h x)⁻¹ ∈ D`), the
conjugation formula `canon_H5` and `canon_H2` (`f(f x) = x`). -/
theorem f_tilde_zs (hsplit : IsSplitRankOne H Q t)
    (hzass : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (C : Work.ZassenhausPSL2.Canon H Q t) {x : Q} (hx : (x : G) ≠ 1) :
    ((C.f (tildeOf C x) : Q) : G)
      = hG C x * (x : G) * (hG C x)⁻¹ := by
  have hxne : ((C.f x : Q) : G) ≠ 1 := canon_f_ne_one hsplit C hx
  have hmem1 : (hG C x)⁻¹ * ((C.f x : Q) : G) * (hG C x) ∈ Q :=
    canon_D_conj_Q_mem_inv hsplit (C.h x) (C.f x)
  have hmem2 : (hG C x) * ((C.f (C.f x) : Q) : G) * (hG C x)⁻¹ ∈ Q :=
    canon_D_conj_Q_mem hsplit (C.h x) (C.f (C.f x))
  have hmem3 : hG C x * (x : G) * (hG C x)⁻¹ ∈ Q :=
    canon_D_conj_Q_mem hsplit (C.h x) x
  have hd : (↑(C.h x))⁻¹ * ((C.f x : Q) : G) * ((↑(C.h x))⁻¹)⁻¹ ∈ Q := by
    simpa [hG, inv_inv] using hmem1
  have hd' : ((↑(C.h x))⁻¹)⁻¹ * ((C.f (C.f x) : Q) : G) * (↑(C.h x))⁻¹ ∈ Q := by
    simpa [hG] using hmem2
  have h5 := canon_H5 hsplit hzass h2 C ((C.h x)⁻¹) (C.f x) hxne hd hd'
  have htil : tildeOf C x = (⟨(hG C x)⁻¹ * ((C.f x : Q) : G) * (hG C x), hmem1⟩ : Q) :=
    Subtype.ext (by simpa [fG, hG] using tildeOf_eq hsplit hzass h2 C hx)
  have heq : (⟨(hG C x)⁻¹ * ((C.f x : Q) : G) * (hG C x), hmem1⟩ : Q)
      = (⟨(↑(C.h x))⁻¹ * ((C.f x : Q) : G) * ((↑(C.h x))⁻¹)⁻¹, hd⟩ : Q) :=
    Subtype.ext (by
      show (hG C x)⁻¹ * ((C.f x : Q) : G) * (hG C x)
        = (↑(C.h x))⁻¹ * ((C.f x : Q) : G) * ((↑(C.h x))⁻¹)⁻¹
      simp [hG, inv_inv])
  have heq2 : (⟨((↑(C.h x))⁻¹)⁻¹ * ((C.f (C.f x) : Q) : G) * (↑(C.h x))⁻¹, hd'⟩ : Q)
      = (⟨hG C x * (x : G) * (hG C x)⁻¹, hmem3⟩ : Q) :=
    Subtype.ext (by
      show ((↑(C.h x))⁻¹)⁻¹ * ((C.f (C.f x) : Q) : G) * (↑(C.h x))⁻¹
        = hG C x * (x : G) * (hG C x)⁻¹
      rw [show ((C.f (C.f x) : Q) : G) = (x : G) from
            congrArg Subtype.val (canon_H2 hsplit C x hx)]
      simp [hG, inv_inv])
  have key : C.f (⟨(hG C x)⁻¹ * ((C.f x : Q) : G) * (hG C x), hmem1⟩ : Q)
      = (⟨hG C x * (x : G) * (hG C x)⁻¹, hmem3⟩ : Q) := by
    rw [heq]
    exact h5.trans heq2
  rw [htil, key]

end Work.ZassenhausSuzuki
