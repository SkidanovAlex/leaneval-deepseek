import Mathlib
import Submission.NK.LocalCFT.Brauer.Basic

/-!
# Non-vanishing of `H²(G_κ, ℤ/p)` versus a surviving finite-level class

The local Brauer input `H²(G_κ, ℤ/p) ≠ 0` is, by construction, a statement about the filtered
colimit `H2Profinite p ⊤ = colim_L H²(Gal(L/κ), ℤ/p)` over the finite Galois intermediate fields
`L` of `κ'` over `κ`, with the *inflation* maps as transition maps
(`NK.BrauerHasse.H2Profinite`).

This module proves that this non-vanishing is equivalent to the existence of a **surviving finite
level class**: a finite Galois extension `L/κ` together with a non-zero class
`a ∈ H²(Gal(L/κ), ℤ/p)` whose inflation to every larger finite Galois level is again non-zero
(`NK.LocalCFT.SurvivingH2Class`).  This is the form in which the classical computation
(Tate local duality / the Demushkin presentation) produces the input, and it is a statement about
finite group cohomology only.

Both directions are formal consequences of the explicit description of the colimit:

* *surviving ⇒ non-vanishing*: if `ofLevel L a = 0`, then `ofLevel_eq_iff` exhibits a finite level
  `M ≥ L` on which the inflation of `a` vanishes — contradicting survival;
* *non-vanishing ⇒ surviving*: an element of the colimit is the class of some finite level `L`,
  and `ofLevel_levelMap` shows that the inflation of its representative to any larger level `L'`
  represents the *same* non-zero colimit class, hence is non-zero.

Note that the `H¹`-vanishing hypothesis of the inflation–restriction sequence is *not* needed here:
the equivalence is a formality about this particular colimit, given that the finite Galois
intermediate fields are directed.  The genuine mathematical content of the local Brauer computation
is the *existence* of a surviving class (equivalently, of a non-zero class at some finite level,
by `NK.LocalCFT.localH2Nonvanishing_iff_finiteLevel`).
-/

universe u

namespace NK.LocalCFT.Brauer

theorem localH2Nonvanishing_iff_surviving {p : ℕ} {κ κ' : Type u} [Field κ] [Field κ']
    [Algebra κ κ'] [IsSepClosure κ κ'] :
    NK.LocalCFT.LocalH2Nonvanishing p κ κ' ↔ NK.LocalCFT.SurvivingH2Class p κ κ' := by
  constructor
  · -- A non-zero class of the colimit is represented at some finite level, and the inflations of
    -- that representative represent the same non-zero class, hence are non-zero.
    rintro ⟨x, hx⟩
    obtain ⟨L, a, rfl⟩ :=
      NK.BrauerHasse.H2Profinite.ofLevel_surjective (K := κ) (K' := κ') (p := p) (U := ⊤) x
    refine ⟨L, a, ?_, ?_⟩
    · intro h0
      exact hx (by rw [h0, NK.BrauerHasse.ofLevel_zero])
    · intro L' h h0
      exact hx (by
        rw [← NK.BrauerHasse.H2Profinite.ofLevel_levelMap (p := p) (U := ⊤) h a, h0,
          NK.BrauerHasse.ofLevel_zero])
  · -- A surviving class is non-zero in the colimit: if its class vanished, its inflation would
    -- die at some larger finite level.
    rintro ⟨L, a, _ha, hsurv⟩
    refine ⟨NK.BrauerHasse.H2Profinite.ofLevel L a, ?_⟩
    intro hzero
    obtain ⟨M, h₁, _h₂, e⟩ :=
      (NK.BrauerHasse.ofLevel_eq_iff (p := p) (U := ⊤) a
        (0 : NK.BrauerHasse.LevelH2 (K := κ) (K' := κ') p ⊤ ⊥)).mp hzero
    exact hsurv M h₁ (by simpa using e)

end NK.LocalCFT.Brauer
