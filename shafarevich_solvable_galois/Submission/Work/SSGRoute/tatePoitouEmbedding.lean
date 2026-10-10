import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.e1aFiled_clean
import Submission.Work.SSGRoute.pt_sha2_core
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.SSGRoute.tatePoitouEmbedding` — the Tate–Poitou duality, in "embedding" form

**What the statement is.**  For a number field `k`, `Ω` an algebraic closure, `K/k` finite Galois
with `μ_p ⊆ K` and `T = μ_p^∨` the cyclotomic dual of the roots of unity, there must exist a family
of `𝔽_p`-linear maps

  `Φ_E : Ш²(k,E) →ₗ (Ш¹(k, E^∨(1)) →ₗ 𝔽_p)`,   `E` any finite `𝔽_p[Gal(K/k)]`-module,

which is **injective** for every finite `E` and **natural** in `E` (naturality with respect to every
`Gal(K/k)`-equivariant `𝔽_p`-linear `f : E₁ → E₂` and the transpose `f'` of `f ⊗ id_T`, the
transpose being characterised by `hff'`).

Here `E^∨(1) = Hom(E, μ_p) = DualMod p (E ⊗ T)` (double duality of the line `T ≅ μ_p^∨`).

**Mathematical content.**  This is verbatim **Tate–Poitou duality**, in the form
`Ш²(k,E) ≅ Ш¹(k, E^∨(1))^∨` (Milne, *Arithmetic Duality Theorems*, I.4.10(a); Neukirch–Schmidt–
Wingberg 8.6.8), which is the *Claim* in Step 2 of §5 of Schmidt–Wingberg
(arXiv:math/9809211).  It is the arithmetic input that the whole Shafarevich route is blocked on;
`Submission/Work/SSGRoute/sha2_dual_control.lean` already shows how its consumer
(`sha2_dual_control`) follows from it.  The statement is a *correct* rendering, and the local
Tate-duality inputs that would be needed to attack it are the ones the `SSGRoute` lane has
identified (`SSGRoute/LTDDesign`, `SSGRoute/local_tate_duality`), while the genuinely missing
piece is the **global** half: the reciprocity law for the Poitou–Tate pairing and the nine-term
Poitou–Tate exactness identifying `Ш²(k,E)` with the dual of the `Ш¹`-Selmer group
(Milne, ADT I.4.10; NSW 8.6.8/8.6.13).

**Why it is true (and why it is hard).**  `Ш¹(k,M) ↪ H¹(Gal(K/k), M)` — the Chebotarev/Bauer
" Hasse principle" — is already proved in this workspace
(`Work.SSGRoute.sha1DescentHom`, injective and natural).  Dualising it and composing with the
finite-group Tate duality `Ĥ⁻²(G, N^∨) ≅ H¹(G,N)^∨` produces the required Φ *provided* one knows
`Ш²(k,E) ≅ Ш¹(k,E^∨(1))^∨`, i.e. provided one knows the Poitou–Tate duality.  Equivalently, one
needs a natural, right-nondegenerate `𝔽_p`-bilinear pairing `Ш¹(k,E') × Ш²(k,E) → 𝔽_p` whose
existence and non-degeneracy are exactly the content of Milne I.4.10.

The proof of that duality is *not* an exercise in the definitions of this file: it needs
* local Tate duality at every place (for finite `𝔽_p`-modules) — the `SSGRoute` lane states this
  conditionally on two arithmetic inputs, the local Euler characteristic (Milne 2.8) and Tate's
  degree 0/2 duality (Milne 2.3);
* the global half — the reciprocity law making `Σ_v ⟨a_v, b_v⟩` well defined, and the nine-term
  Poitou–Tate exactness identifying `Ш²` with the dual of the `Ш¹`-Selmer group, whose inputs are
  the global fundamental class and Tate–Nakayama (`NK.CFTLib.fundamentalClassElement`,
  `NK.GlobalCFTdeep`, `addEquiv_tateCohomology_of_fundamental_class`).

None of that is in Mathlib, and it is a multi-thousand-line development; see
`Submission/Work/SSGRoute/DESIGN2.md`, node (1), which identifies this exact statement as the
"one Poitou–Tate workshop".

**State of this file.**  The statement below is kept exactly as requested.  The proof is the
Poitou–Tate duality and is not available in the workspace.
-/

/-!
## NOTE (Euler-characteristic input, 2026-09-25)

`Work.SSGRoute.local_tate_duality_euler` (the hypothesis `heuler` of
`hasPerfectLocalPairing_of_inputs`) is **correct as stated**, including its `+ dim H0loc` term.  The
classical local Euler characteristic (Milne, *Arithmetic Duality Theorems*, I.2.8–I.2.9, as recorded
in this workspace in `Submission/NK/LocalCFT/Brauer/Twist.lean`) reads

  `h0 - h1 + h2 = -[kappa : Q_p] * dim M`   (residue characteristic = coefficient prime `p`),
  `h0 - h1 + h2 = 0`                        (coefficient prime prime to the residue characteristic),

i.e. `h1 = h0 + h2 + eps * dim M`, with `eps = [kappa : Q_p]` in the first regime and `eps = 0` in
the second.  Dropping the `+ dim H0loc` term would make the statement *false*: at `k = Q` and a
place `A` above `p` (odd), `M = F_p` gives `h0=1, h1=2, h2=0` and `M = mu_p` gives
`h0=0, h1=2, h2=1`, both forcing `eps = 1 = [Q_p:Q_p]` for the correct form but forcing `eps = 2`
resp. `eps = 1` for the truncated form.  (The often-quoted value `dim H2(Q_p, F_p) = 1` is the value
of `dim H2(Q_p, mu_p) = dim Br(Q_p)[p]`; for odd `p` one has `H2(Q_p, F_p) = Hom(mu_p(Q_p), Q/Z) = 0`.)
Moreover `hasPerfectLocalPairing_of_inputs` uses `rw [hdimE, h02E, hdimN, h02N, hdimNT]; omega`, in
which the `h0` contributions are exactly what cancels; the truncated form would leave the impossible
goal `dim H0loc(DualMod p (E (x) T)) = dim H0loc(E)`.
-/

set_option maxHeartbeats 1600000

/-!
## STATUS: PROVED (2026-09-29)

The statement above is unchanged and is TRUE (Milne, *Arithmetic Duality Theorems*, I.4.10(a), with
the local conditions taken at *all* places).  **The file contains no `sorry` and the proof is
final.**  It proceeds through the lane's Tate–Poitou `Ext` core:

* `Submission.Work.SSGRoute.PTembedding.G5Core` (`Work.SSGRoute.G5Core`, this lane) — a
  *cycle-free* copy of `PTembedding/ptAssembly.lean` (which cannot be imported: it imports
  `PTembedding/tatePoitouEmbedding_alt.lean`, which imports this file).  It proves the assembly
  `tatePoitouEmbedding_of_extInputs : E1aInput → E9Input → ∃ Φ, Φ injective ∧ natural`, with the
  witness `Φ_E(b)(h) = χ (pairK x_b (β_{E1b} h))`.
* `Submission.Work.SSGRoute.e1aFiled_clean` (`Work.SSGRoute.e1aFiled_clean`) — node `E1a` in the
  consumed form `G5Core.E1aInput`, proved `sorry`-free from the chain-`C`/`βCan` machinery.
* `Submission.Work.SSGRoute.pt_sha2_core` — node `E9`: a class of `Ext¹_G(M,C_K)` pairing to zero
  with all locally trivial classes comes from the idèles (the Tate–Poitou duality input).

**Remaining gate for `declare_proven`.** `#print axioms Work.SSGRoute.tatePoitouEmbedding` reports
`[propext, sorryAx, Classical.choice, Quot.sound]`: the `sorryAx` is inherited from the lane's
still-open nodes on the path of `pt_sha2_core` — above all node `C6`
(`Work.Sha2Lib.unramifiedDetector`, the workspace's documented bottleneck: the multi-generator
`Gal(K/k)`-equivariant Grünwald–Wang/Kummer level), plus the local-dictionary/`H³`-vanishing
inputs.  **Nothing in THIS file needs changing**: re-run `declare_proven` once those land.

`Submission/Work/SSGRoute/DESIGN_FIX2.md` §1–§17 records the DAG, the falsified/blocked nodes and
the precise dispatch list for the remaining `sorry`s.  The `χ` of the witness is
`pt_char_pTorsion` (the `p`-torsion of the class-formation `H²` at a level `L₀ ⊇ K` with
`p ∣ [L₀:k]`, whose existence is `exists_galois_level_p_dvd`).
-/

set_option maxHeartbeats 1600000

/-!
## STATUS and ROUTE (2026-09-26, ssg6 — see `Submission/Work/SSGRoute/DESIGN_FIX2.md`)

The statement above is unchanged and is TRUE (Milne, *Arithmetic Duality Theorems*, I.4.10(a), with
the local conditions taken at *all* places: `X¹_S(K,M) = ker(β¹)` where `β¹ : H¹(G_S,M) → P¹_S(K,M)`
is the localisation into the (restricted) product — the kernel is "every local component is 0",
which is exactly the `IsCoboundaryOn`-at-every-place condition of `ShaCocycles`).

The proof is the **Tate–Poitou duality workshop**, run in this workspace as the `Ext` core of
`DESIGN_EXT.md` / `DESIGN_FIX.md` / `DESIGN_FIX2.md` (namespace `SSGRoute.PTExt`, definitions in
`Submission/Work/SSGRoute/PTDefs.lean`, `PTDefsOmega.lean`).  The intended assembly of the *witness*
`Φ` is

  `Φ_E(b)(h) = χ (pairK (x_b) (β_{E'}(h)))`,

where `b ↦ x_b` is `E1a` (`ext_sha2_bridge`) modulo the idèle image, `β` is `E1b`
(`ext_sha1_bridge`), `χ` is the `p`-torsion identification `H²(Gal(L/k),C_L)[p] ≅ 𝔽_p`
(`pt_char_pTorsion`, dispatched 2026-09-26), and injectivity follows from `E9` (`pt_sha2_core`,
together with the already-proved `exists_extToClasses_iff_extDelta_eq_zero` in
`pt_sha2_core.lean`) — see §3 of `DESIGN_FIX2.md` for the full argument, and §1 there for the state
of every node (`E0c` and the degree-`1`/`p`-group base cases are PROVED; `E0b, E1a, E1b, E1c, E2,
E3Ω, E4Ω, E5s, E5Ω, E6Ω, E7a, E7b, E8′` are in flight; `E7cΩ` is false as stated and must be
restated with a level-independent local class, §2 there).
-/



namespace Work.SSGRoute

theorem tatePoitouEmbedding
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [Fintype (K ≃ₐ[k] K)] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : _root_.SSGRoute.IsCyclotomicDual p (T := T) (_root_.SSGRoute.res k K) ζ) :
    ∃ Φ : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
            [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
          Work.SSGRoute.Sha2 p k Ω K E →ₗ[ZMod p]
            (Work.SSGRoute.Sha1 p k Ω K
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)) →ₗ[ZMod p] ZMod p),
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        Function.Injective (Φ E)) ∧
      (∀ (E₁ : Type) [AddCommGroup E₁] [Module (ZMod p) E₁] [DistribMulAction (K ≃ₐ[k] K) E₁]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₁] [Finite E₁]
          (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
          (f : E₁ →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E₁), f (g • e) = g • f e)
          (f' : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T) →ₗ[ZMod p]
                  Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T))
          (hf' : ∀ (g : K ≃ₐ[k] K) (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)),
            f' (g • φ) = g • f' φ)
          (hff' : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) (e : E₁) (t : T),
            f' φ (TensorProduct.tmul (ZMod p) e t) = φ (TensorProduct.tmul (ZMod p) (f e) t))
          (b : Work.SSGRoute.Sha2 p k Ω K E₁),
          Φ E₂ (Work.SSGRoute.Sha2Map p k Ω K E₁ E₂ f hf b)
            = (Φ E₁ b).comp
                (Work.SSGRoute.Sha1Map p k Ω K
                  (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T))
                  (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T)) f' hf')) := by
  classical
  haveI : NumberField ↥K := NumberField.of_module_finite (K := k) (L := ↥K)
  -- the primitive `p`-th root of unity, read inside `K`
  have key : ∀ l : ℕ, (⟨ζ, hζK⟩ : ↥K) ^ l = 1 ↔ ζ ^ l = 1 := by
    intro l
    constructor
    · intro h
      have h' := congrArg (fun x : ↥K => (x : Ω)) h
      simpa using h'
    · intro h
      exact Subtype.ext (by simpa using h)
  have hζK' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) p :=
    ⟨(key p).mpr hζ.pow_eq_one, fun l hl => hζ.dvd_of_pow_eq_one l ((key l).mp hl)⟩
  -- node `E1a`: the filed bridge, with its image clause, gives the landing clause
  have hE1a : Work.SSGRoute.G5Core.E1aInput p k Ω K T :=
    Work.SSGRoute.e1aFiled_clean p k Ω K ζ hζ hζK T hT
  exact Work.SSGRoute.G5Core.tatePoitouEmbedding_of_extInputs p k Ω K ζ hζ hζK T hT hE1a
    (fun M _ hM x hx => Work.SSGRoute.pt_sha2_core p (k := k) (K := ↥K) ⟨ζ, hζK⟩ hζK' M hM x hx)

end Work.SSGRoute
