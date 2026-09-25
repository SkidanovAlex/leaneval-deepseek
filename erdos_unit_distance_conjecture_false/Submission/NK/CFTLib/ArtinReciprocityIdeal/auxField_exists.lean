import Mathlib
import Submission.NK.CFTLib.ARL.AuxField
import Submission.NK.CFTLib.ArtinReciprocityIdeal.LangDefs
import Submission.NK.CFTLib.ARL.auxiliary_field_single
import Submission.NK.CFTLib.ARL.exists_mod_order_independent
import Submission.NK.CFTLib.ARL.auxField_exists_B

namespace NK.CFTLib.ArtinReciprocityIdeal

open NumberField IsDedekindDomain
open scoped NumberField

/-- **Existence of the auxiliary fields of Artin's trick** (Lang, *Algebraic Number Theory*,
Ch. X §2, the auxiliary-field construction and the "Contention").

For a finite **cyclic** extension `L/K` of number fields and any `m > 0`, the corrected
auxiliary-field interface `NK.CFTLib.ARL.AuxFieldHyp K L m` holds: for every finite set `s` of
primes of `K` prime to `(m)` and every finite set `S` of rational primes there are `M ≥ 1`
(coprime to `m`, avoiding `S` and all `absNorm 𝔭`, `𝔭 ∈ s`) and intermediate fields
`E_𝔭 ≤ E` of the cyclotomic field `L(ζ_M)`, such that

* `E ∩ L = K` and `E_𝔭 · ℚ(ζ_M) = L(ζ_M)` for every `𝔭 ∈ s` (so `L ⊆ E_𝔭(ζ_M)`, i.e. `L·E_𝔭/E_𝔭`
  is a subextension of the cyclotomic extension `E_𝔭(ζ_M)/E_𝔭`);
* `𝔭` splits completely in `E_𝔭/K`.

Construction: write `M = ∏_{𝔭 ∈ s} q_𝔭` with distinct large primes `q_𝔭`
(`NK.CFTLib.ARL.exists_mod_order_independent`, van der Waerden's second result), so that
`Gal(L(ζ_M)/K) ≅ G × (ℤ/M)^×` and `Gal(K(ζ_M)/K) = ∏_𝔭 Gal(K(ζ_{q_𝔭})/K)` (CRT), with
`L ∩ K(ζ_M) = K` and `K ∩ ℚ(ζ_M) = ℚ` (choose `q_𝔭` coprime to `disc K · disc L`).  For each
`𝔭` let `Δ'_𝔭 = ∏_{𝔮 ≠ 𝔭} Gal(K(ζ_{q_𝔮})/K)` and
`E_𝔭 = Ω^{⟨(σ,τ_𝔭), Φ_𝔭⟩·Δ'_𝔭}` where `σ` generates `G = Gal(L/K)`, `Φ_𝔭` is the Frobenius at
`𝔭` (with `(ℤ/M)^×`-component `N𝔭 mod M`) and `τ_𝔭 ∈ Gal(K(ζ_{q_𝔭})/K)` has order divisible by
`n = [L:K]` and is independent of the Frobenius: then `E_𝔭 ∩ L = K`, `E_𝔭·ℚ(ζ_M) = L(ζ_M)` and
`𝔭` splits completely in `E_𝔭`.  Finally `E = Ω^{⋂_{𝔭 ∈ s} (⟨(σ,τ_𝔭), Φ_𝔭⟩·Δ'_𝔭)}` is the
compositum of the `E_𝔭`, and `proj_G(⋂_𝔭 (⟨(σ,τ_𝔭), Φ_𝔭⟩·Δ'_𝔭)) ∋ σ`, whence `E ∩ L = K`. -/
theorem auxField_exists (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (m : ℕ) (hm : 0 < m) : NK.CFTLib.ARL.AuxFieldHyp K L m := by
  exact NK.CFTLib.ARL.auxField_exists_B K L m hm

end NK.CFTLib.ArtinReciprocityIdeal
