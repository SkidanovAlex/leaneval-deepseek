import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.PTCore.X1_unramified
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTCore

/-- The load-bearing inclusion of the corrected item (3) of the bridge: if `S` contains every finite
place at which `K/k` is ramified, **up to conjugacy**, then every locally trivial cocycle is
unramified outside `S` — `Z1loc ≤ Z1unr S`.  This is the `⊇` half of `Ш¹ ≤ X¹_S`: with it, the
submodule `X1 S` of the ambient `H¹_cont` (= the image of `Z1unr S ⊓ Z1locOn S`, built by the prover
via `Submodule.map`/`comap` over `↥(lcCocycles ⊤)`) contains the image of `Ш¹`.

Proof shape (both reviewers of the literal-membership version confirmed it, and it is unchanged):
for a finite place `B` whose conjugacy class misses `S`, the contrapositive of `hS` gives
`¬ IsRamifiedIn k K B`, i.e. `I_B ⊆ K.fixingSubgroup = ker (res k K)`, hence `res k K σ = 1` for
`σ ∈ I_B`; `Z1loc` gives `IsCoboundaryOn (res k K) (decomp k B) a`, so
`a σ = res k K σ • m − m = 1 • m − m = 0`.  The cocycle and local-constancy clauses of `Z1unr` come
straight from `Z1loc`.

The hypothesis is needed (and is *satisfiable* only in the conjugacy form): for arbitrary `S` the
global coboundary `σ ↦ σ • m − m` with `m ∉ M^{I_B}` lies in `Z1loc` but not in `Z1unr S`
(`PTCore/STATUS_pt_pairing_left_inj_s7.md` §13), while a `Finset` of places can cover the infinitely
many places above a ramified prime only up to conjugacy (§27). -/
theorem Z1loc_le_Z1unr_of_ramified_subset
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (S : Finset (ValuationSubring Ω))
    (hS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      SSGRoute.IsRamifiedIn k K B → ∃ A ∈ S, SSGRoute.IsConjPlace k A B) :
    Work.SSGRoute.Z1loc p k Ω K M ≤ Work.SSGRoute.PTCore.Z1unr p k Ω K M S := by
  intro a ha
  obtain ⟨h1, h2, h3, h4⟩ := ha
  refine ⟨h1, h2, ?_⟩
  intro B hBfin hBconj σ hσ
  -- No conjugate of `B` lies in `S`, and `hS` covers the ramified places: so `B` is unramified
  -- in `K/k`, whence every inertia element of `B` lies in `K.fixingSubgroup = ker (res k K)`.
  have hσfix : σ ∈ K.fixingSubgroup := by
    by_contra hcon
    obtain ⟨A, hA, hAconj⟩ := hS B hBfin ⟨σ, hσ, hcon⟩
    exact hBconj A hA hAconj
  obtain ⟨m, hm⟩ := h3 B hBfin
  have hres : SSGRoute.res k K σ = 1 := by
    rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker K]
    exact hσfix
  rw [hm σ hσ.1, hres, one_smul, sub_self]

end Work.SSGRoute.PTCore
