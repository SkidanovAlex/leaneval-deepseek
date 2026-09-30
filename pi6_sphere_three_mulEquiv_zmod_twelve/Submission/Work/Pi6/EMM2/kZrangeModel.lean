import Mathlib
import Submission.Work.Pi6.EMM2.kZchain
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `kZ Y (M - 2)` is a range model of `K(ℤ,2)` (area EMM2)

`kZ Y k` is `Y` with `k` rounds of "kill `π_{m+2}` by attaching `(m+3)`-cells", `m = 2, …, k+1`
(`Submission/Work/Pi6/EMM2/kZchain.lean`): `kZ Y k` keeps `π_0, π_1, π_2` and kills
`π_3, …, π_{k+2}`.

Consequently, if `Y` has trivial `π_0` and `π_1` and `π_2 ≅ ℤ`, then `kZ Y (M - 2)` — the space in
which all homotopy of `Y` in degrees `3` through `M` has been killed — is a range model of
`K(ℤ,2)` up to degree `M`.

This is the range-model statement underlying the `K(ℤ,2)` step of the EMM2 forcing argument: it
packages `kZchain.kZ_pi_subsingleton` (the killed degrees) and `kZchain.kZUp_pi_bijective` (the
`π_i`, `i ≤ 2`, transported along the inclusion `kZUp`).
-/

namespace Work.Pi6.EMM2

noncomputable section

/-- **Subsingleton transfers along a bijection.**  (The Mathlib form
`Function.Surjective.subsingleton` takes the hypothesis as an instance.) -/
private theorem subsingleton_of_bijective {A B : Type} (f : A → B)
    (hf : Function.Bijective f) (hA : Subsingleton A) : Subsingleton B :=
  ⟨fun b b' => by
    obtain ⟨a, rfl⟩ := hf.2 b
    obtain ⟨a', rfl⟩ := hf.2 b'
    rw [Subsingleton.elim a a']⟩

/-- **`kZ Y (M - 2)` is a range model of `K(ℤ,2)` up to degree `M`.**  The isomorphism on `π_2` is
the bijection `kZUp_pi_bijective` converted into a `≃*` by `MulEquiv.ofBijective` and composed with
the given `π_2 Y ≅ ℤ`; the vanishing in degrees `0` and `1` is transported along the inclusion, and
the vanishing in degrees `3, …, M` is `kZ_pi_subsingleton`. -/
theorem kZrangeModel {Y : Type} [TopologicalSpace Y] (y₀ : Y) (M : ℕ) (hM : 3 ≤ M)
    (h0 : Subsingleton (HomotopyGroup (Fin 0) Y y₀))
    (h1 : Subsingleton (HomotopyGroup (Fin 1) Y y₀))
    (h2 : Nonempty (HomotopyGroup (Fin 2) Y y₀ ≃* Multiplicative ℤ)) :
    Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) M (Work.Pi6.EMM2.kZ Y (M - 2))
      (Work.Pi6.EMM2.kZUp Y (M - 2) y₀) := by
  constructor
  · -- `π_2`: `π_2 Y ≅ ℤ` composed with the bijective (hence iso) map induced by `kZUp`.
    obtain ⟨e⟩ := h2
    have hbij := kZUp_πmap_bijective (Y := Y) (M - 2) 1 (by norm_num) y₀
    have iso : HomotopyGroup (Fin 2) Y y₀ ≃*
        HomotopyGroup (Fin 2) (kZ Y (M - 2)) (kZUp Y (M - 2) y₀) :=
      MulEquiv.ofBijective (Work.StemsB.πmap (kZUp Y (M - 2)) 1 y₀) hbij
    exact ⟨iso.symm.trans e⟩
  · -- vanishing in the other degrees
    intro i hi hc
    rcases lt_or_ge i 2 with hlt | hge
    · -- `i = 0, 1`: transport along the inclusion `kZUp`
      interval_cases i
      · exact subsingleton_of_bijective _
          (kZUp_pi_bijective (Y := Y) (M - 2) 0 (by norm_num) y₀) h0
      · exact subsingleton_of_bijective _
          (kZUp_pi_bijective (Y := Y) (M - 2) 1 (by norm_num) y₀) h1
    · -- `3 ≤ i ≤ M`: killed by the tower
      have hi3 : 3 ≤ i := by omega
      have hiM : i ≤ M := hc.resolve_left (by omega)
      exact kZ_pi_subsingleton (Y := Y) (M - 2) (kZUp Y (M - 2) y₀) i hi3 (by omega)

end

end Work.Pi6.EMM2
