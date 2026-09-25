import Mathlib
import Submission.NK.LocalReciprocityLubinTate.LubinTate.LevelSimplicity
import Submission.NK.LocalReciprocityLubinTate.LubinTate.finrank_LTLevel_eq_of_isSimple
import Submission.NK.LocalReciprocityLubinTate.LubinTate.isGalois_LTLevel
import Submission.NK.LocalReciprocityLubinTate.LubinTate.finiteDimensional_LTLevel

/-!
# The order of the Galois group of a Lubin–Tate level

The `n`-th Lubin–Tate level `K_n = F(Λ_n)` is a finite Galois extension of `F`
(`isGalois_LTLevel`, `finiteDimensional_LTLevel`), so its group of `F`-automorphisms has order
equal to the degree `[K_n : F]` (`IsGalois.card_aut_eq_finrank`).  Under the simplicity hypothesis
`LTLevelIsSimple F π q n`, that degree was computed in
`NK.LocalReciprocityLubinTate.LubinTate.finrank_LTLevel_eq_of_isSimple` to be `(q-1)q^{n-1}`.
Hence

`#Gal(K_n/F) = #(K_n ≃ₐ[F] K_n) = (q-1)q^{n-1}`.

This is the order input for the local reciprocity isomorphism of the Lubin–Tate theory
(Milne, *CFT*, §I.3; Serre, *Local Fields*, Ch. XV §4).
-/

namespace NK.LocalReciprocityLubinTate.LubinTate

open Polynomial

universe u

theorem card_aut_LTLevel_eq_of_isSimple (F : Type u) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (π : (↥(ValuativeRel.valuation F).integer)) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (hn : 1 ≤ n) (h : NK.LocalReciprocityLubinTate.LTLevelIsSimple F (π : F) q n) :
    Nat.card (↥(NK.LocalReciprocityLubinTate.LTLevel F (π : F) q n) ≃ₐ[F]
        ↥(NK.LocalReciprocityLubinTate.LTLevel F (π : F) q n)) = (q - 1) * q ^ (n - 1) := by
  haveI : FiniteDimensional F ↥(NK.LocalReciprocityLubinTate.LTLevel F (π : F) q n) :=
    finiteDimensional_LTLevel F (π : F) q n hq
  haveI : IsGalois F ↥(NK.LocalReciprocityLubinTate.LTLevel F (π : F) q n) :=
    isGalois_LTLevel F (π : F) q n hq
  rw [IsGalois.card_aut_eq_finrank]
  exact finrank_LTLevel_eq_of_isSimple F π hπ q n hq hn h

end NK.LocalReciprocityLubinTate.LubinTate
