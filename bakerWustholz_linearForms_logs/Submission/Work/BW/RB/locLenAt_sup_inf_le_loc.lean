import Mathlib
import Submission.Work.BW.BWGradedBase
import Submission.Work.BW.colon_localize_length_add
import Submission.Work.BW.RB.length_cut_kernel_le_tor
import Submission.Work.BW.RB.length_ker_lsmul_le_quot

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

/-! Guidance from the project lead (the requester):

LEAD 09-30 00:00: the local-length subadditivity. VERDICT below: FALSE for an arbitrary CommRing, TRUE with [IsNoetherianRing R]. Proof: Mayer–Vietoris gives ℓ(LHS)=ℓ(A+P)+ℓ(C+P)−ℓ(A+C+P)+ℓ(K); ℓ(K) ≤ ℓ(P-torsion of R/(A+C)) (length_cut_kernel_le_tor, any ring) ≤ ℓ(N/PN) (length_ker_lsmul_le_quot, Noetherian module) = ℓ(R/(A+C+P)). length_sup_inf_span_le combines them with mv_length; the localized locLenAt_sup_inf_le_loc then follows via IsLocalization.map_inf / Ideal.map_sup / Ideal.map_span. Do NOT try the general-ring version: it is false.

# Verdict: locLenAt_sup_inf_le_loc (sorry A) and primLen_sup_span_le_sum (sorry B)

Date 2026-09-29. Workspace: 3.144.32.173, fundmath3-runs/bakerWustholz_linearForms_logs.

## 1. Is (A) true as stated?

**It is false as stated (arbitrary `CommRing R`). It is true once `[IsNoetherianRing R]` is added.**
No other hypothesis is needed: no primary components, no nonzerodivisor condition, no condition on q.
The `hfin` hypothesis is also unnecessary.

### Exact accounting (any commutative ring S, here S = R_q, a = A S, c = C S, p = P/1)

Let K be the kernel of S/((a∩c)+(p)) → S/((a+(p))∩(c+(p))). Then

    ℓ(S/((a∩c)+p)) = X + ℓ(K),         X := ℓ(S/((a+p)∩(c+p)))
    X + ℓ(S/(a+c+p)) = ℓ(S/(a+p)) + ℓ(S/(c+p))     (Mayer–Vietoris, `mv_length`)
    K ≅ ((a+c):p) / ((a:p)+(c:p)),  a quotient of  0 :_{S/(a+c)} p.

You were right that K ≠ 0 in general. But K is always paid for by the term ℓ(S/(a+c+p)).
The inequality reduces to

    ℓ(0 :_N p) ≤ ℓ(N/pN),   N = S/(a+c).

This holds for every Noetherian module N. Let T = ker(p^n) be where the chain ker(p^k) stabilizes.
Then T/pT injects into N/pN, T has finite length, and ℓ(ker p|_T) = ℓ(T/pT).
It fails for non-Noetherian N; the Prüfer module E = Frac(D)/D over a DVR is the standard example.

Small Noetherian example, k[x,y] at (x,y), with A=(x), C=(y), P=x+y:
- ℓ(K) = 1 (K = (x,y)/(xy,x+y)), and ℓ(R/(A+C+P)) = 1.
- LHS ℓ(k[x]/x²) = 2 and RHS 1+1 = 2.
- The kernel is nonzero and the inequality is exactly tight. No Noetherian counterexample exists (proof below).

### Counterexample for general R (idealization; R is local, not Noetherian)

- D = k[t]_(t) (DVR), E = Frac(D)/D (the Prüfer module), M = D² ⊕ E², R = D ⋉ M (trivial extension, M² = 0).
- R is local with maximal ideal q = tD ⋉ M. Take P = (t,0).
- A = 0 ⋉ X with X = D² ⊕ 0.
- C = 0 ⋉ Y with Y = {(d, ψ d) : d ∈ D²}, where ψ(d₁,d₂) = (d₁/t, d₂/t) mod D ∈ E².

The ingredients:
- PR = tD ⋉ (tD² ⊕ E²), because E is divisible.
- A + PR = tD ⋉ M and C + PR = tD ⋉ M, so ℓ(R/(A+P)) = ℓ(R/(C+P)) = 1.
- A ∩ C = 0 ⋉ (X∩Y) = 0 ⋉ (tD² ⊕ 0), so (A∩C)+PR = tD ⋉ (tD² ⊕ E²).
- Therefore ℓ(R/((A∩C)+P)) = 1 + ℓ(D²/tD²) = **3 > 2 = 1 + 1**.
- R is local, so R_q = R and locLenAt equals these lengths. hfin holds (3 ≠ ⊤).

The failure sits in the torsion step. N = R/(A+C) = D ⋉ E² has ℓ(0:_N t) = 2 but ℓ(N/tN) = 1. (D = ℤ_(p), k = 𝔽_p works the same way.)

So the Lean statement in `RB/locLenAt_sup_inf_le_loc.lean` cannot be proved. The variant `BW/locLenAt_sup_inf_le` (general R) and the `_clean` variant cannot be proved either, if the latter is also stated for general R.

The `arith_aux` route in `BW/locLenAt_sup_inf_le.lean` has a further problem, independent of truth. It cancels ℓ_q(R/((A∩C):P)) and ℓ_q(R/(A+C)). At the call site these are ⊤ (J has height r, and q has height r+1 over J+(P)). So both of its sorries, the `hdeg` branch and the `Cc+Dd=⊤` branch, are the generic case. Abandon that route.

## 2. What the callers need

There is one caller: `finset_inf_sup_le_sum` in `RB/primLen_sup_span_le_sum_loc.lean`.
- It is declared in `section General` (arbitrary CommRing R) and used only at R = MR N, which is Noetherian.
- It iterates the step over a primary decomposition of J. The step is applied to `a` and to `s.inf id`, a partial intersection. So the components are **not** two primaries, and no primary/CM structure is available or needed.
- The only thing it needs is Noetherianity.

**Change required** (lead or prover, in Submission — not done by me):
1. Add `[IsNoetherianRing R]` to `locLenAt_sup_inf_le_loc`. The statement is in `locLenAt_sup_inf_le_loc.stmt`; it is otherwise identical and keeps `hfin`.
2. Add `[IsNoetherianRing R]` to `finset_inf_sup_le_sum` (lemma-level binder). Its one use, in `primLen_sup_span_le_sum_loc` at `MR N`, then resolves the instance automatically.

### Proof plan (three helper statements, each a `.stmt` here; all four elaborate against the workspace)

1. `length_cut_kernel_le_tor` (any CommRing S):
   `ℓ(S/((a⊓c)+(p))) ≤ ℓ(S/((a+(p))⊓(c+(p)))) + ℓ(ker (p• on S/(a⊔c)))`.
   - Set W = {(a₁,c₁,t) ∈ a×c×S | c₁ − a₁ = t p}.
   - h : W ↠ K, (a₁,c₁,t) ↦ [c₁]. It is surjective: for x = a₀+rp = c₀+sp use (a₀,c₀,r−s).
   - g : W → tor, (a₁,c₁,t) ↦ [t].
   - ker g ≤ ker h: if t = u+v with u∈a, v∈c, then c₁ − vp = a₁ + up ∈ a⊓c.
   - Hence ℓ(K) ≤ ℓ(W/ker g) ≤ ℓ(tor). Close with `Module.length_eq_add_of_exact` on 0→K→…→…→0.
2. `length_ker_lsmul_le_quot` ([IsNoetherian S N]): `ℓ(ker (x•)) ≤ ℓ(N ⧸ range (x•))`.
   - Stabilize ker(x^n) (`monotone_stabilizes`) and set T = ker(x^n).
   - T/xT ↪ N/xN, because t = xm with t ∈ T gives m ∈ ker x^{n+1} = T.
   - ℓ(T) ≤ n·ℓ(T/xT) via the filtration xⁱT.
   - Then ℓ(ker) = ℓ(T/xT) by the two length decompositions of the finite-length T.
3. `length_sup_inf_span_le` ([IsNoetherianRing S]): combine.
   - LHS ≤ X + tor (step 1).
   - tor ≤ ℓ(N/pN) = ℓ(S/((a⊔c)+(p))) (step 2 with N = S/(a⊔c); identify N/pN via `DoubleQuot`).
   - X + that = RHS by `mv_length (a⊔(p)) (c⊔(p))`, using (a⊔(p))⊔(c⊔(p)) = (a⊔c)⊔(p).
   - This is monotone ℕ∞ arithmetic with no cancellation, so no finiteness is needed.
4. `locLenAt_sup_inf_le_loc`: unfold locLenAt and rewrite with `IsLocalization.map_inf`, `Ideal.map_sup`, `Ideal.map_span`, `Set.image_singleton`. Localization.AtPrime of a Noetherian ring is Noetherian (instance). Apply 3.

`locSliceDefs.lean` already has `torOf`/`imOf` and the diag/diff maps, which match this route. `mv_length` exists (public as `Work.BW.mv_length` in `BW/locLenAt_sup_inf_le.lean`, and private in `RB/locLenAt_sup_inf_le_clean.lean`).

## 3. Status of (B) `primLen_sup_span_le_sum` (RB/srel_cut_unmixed.lean:88)

**Not on the critical path.** srel_cut_unmixed.lean is in the import closure (Srel_spanned_le_clean ← Srel_spanned_le ← srel_le_of_generic_chain ← srel_chain_step ← srel_cut_unmixed). But srel_chain_step only uses `finset_sum_le_srel`, `srel_sup_span_le_rayDeg` and `mem_minimalPrimes_sup_span_of_le` from it, and none of those uses the sorry. The sorry is used only by `cut_term_le`, `cut_term_le'` and `srel_cut_unmixed` itself, on the abandoned hunmixed route.

I checked this with a Lean constant-graph walk over the built oleans (`_lead/_loclen_sorrydeps.lean` on the box). The only `sorryAx`-carrying constant reachable is `Work.BW.RB.locLenAt_sup_inf_le_loc`, both from `Work.BW.RB.Srel_spanned_le_clean` and from `Work.BW.refined_bezout`. Caveat: the refined_bezout olean is from 21:12, the clean one from 21:15.

Options for (B):
- Leave it; it does not affect the axioms of the final theorem.
- Or, for hygiene, delete `primLen_sup_span_le_sum`, `cut_term_le`, `cut_term_le'`, `srel_cut_unmixed` from that file.
- Or discharge it from `primLen_sup_span_le_sum_loc`. `hunmixed` implies `hloc`, as the docstring there says.

**Net: after the Noetherian fix, the whole closure depends on exactly one open fact, `length_sup_inf_span_le`. It is true, and it splits into two elementary pieces.**
-/

namespace Work.BW.RB

/-! ## Auxiliary ring-level lemmas

The following are the Mayer--Vietoris identity for ideal lengths and the reduction of the
torsion term of `length_cut_kernel_le_tor` to `ℓ(S ⧸ ((a ⊔ c) ⊔ (p)))`.  They are reproduced
here (with `private` names) so that this file does not depend on `RB/length_sup_inf_span_le.lean`,
which is edited elsewhere. -/

private theorem mv_length {S : Type*} [CommRing S] (I J : Ideal S) :
    Module.length S (S ⧸ (I ⊓ J)) + Module.length S (S ⧸ (I ⊔ J))
      = Module.length S (S ⧸ I) + Module.length S (S ⧸ J) := by
  set f : S →ₗ[S] (S ⧸ I) × (S ⧸ J) :=
    (I : Submodule S S).mkQ.prod (J : Submodule S S).mkQ with hf_def
  have hker : f.ker = (I ⊓ J : Ideal S) := by
    rw [hf_def, LinearMap.ker_prod, Submodule.ker_mkQ, Submodule.ker_mkQ]
  set φ : S ⧸ (I ⊓ J) →ₗ[S] (S ⧸ I) × (S ⧸ J) :=
    (I ⊓ J : Submodule S S).liftQ f (le_of_eq hker.symm) with hφ_def
  have hφval : ∀ x : S, φ (Submodule.mkQ (I ⊓ J : Submodule S S) x)
      = (Submodule.mkQ I x, Submodule.mkQ J x) := by
    intro x; rw [hφ_def, Submodule.mkQ_apply, Submodule.liftQ_apply]; rfl
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, hφ_def, Submodule.ker_liftQ_eq_bot]
    exact le_of_eq hker
  set ψ : (S ⧸ I) × (S ⧸ J) →ₗ[S] S ⧸ (I ⊔ J) :=
    (Submodule.factor (le_sup_left : I ≤ I ⊔ J)).comp (LinearMap.fst _ _ _) -
    (Submodule.factor (le_sup_right : J ≤ I ⊔ J)).comp (LinearMap.snd _ _ _) with hψ_def
  have hψval : ∀ x y : S, ψ (Submodule.mkQ I x, Submodule.mkQ J y)
      = Submodule.mkQ (I ⊔ J : Submodule S S) (x - y) := by
    intro x y
    rw [hψ_def]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, Submodule.factor_mk, map_sub]
  have hψsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I ⊔ J : Submodule S S) z
    refine ⟨(Submodule.mkQ I x, 0), ?_⟩
    rw [show (0 : S ⧸ J) = Submodule.mkQ J 0 from (map_zero _).symm, hψval]; simp
  have hexact : Function.Exact φ ψ := by
    rw [LinearMap.exact_iff]
    apply le_antisymm
    · rintro ⟨a, b⟩ h
      rw [LinearMap.mem_ker] at h
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective I a
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective J b
      rw [hψval] at h
      have hxy : x - y ∈ (I ⊔ J : Ideal S) := Ideal.Quotient.eq_zero_iff_mem.mp h
      obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp hxy
      refine ⟨Submodule.mkQ (I ⊓ J : Submodule S S) (x - i), ?_⟩
      rw [hφval]
      have hz1 : Submodule.mkQ I (x - i) = Submodule.mkQ I x := by
        rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]; simpa using hi
      have hz2 : Submodule.mkQ J (x - i) = Submodule.mkQ J y := by
        rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
        have h2 : j = (x - y) - i := by rw [← hij]; ring
        have : (x - i) - y = j := by rw [h2]; ring
        rw [this]; exact hj
      rw [hz1, hz2]
    · rintro ⟨a, b⟩ ⟨c, hc⟩
      rw [← hc, LinearMap.mem_ker]
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I ⊓ J : Submodule S S) c
      rw [hφval, hψval]; simp
  have hlen := Module.length_eq_add_of_exact φ ψ hφinj hψsurj hexact
  rw [Module.length_prod] at hlen
  exact hlen.symm

/-- The range of multiplication by `p` on `S ⧸ M` is the image of `(p)` in `S ⧸ M`. -/
private theorem range_lsmul_eq {S : Type*} [CommRing S] (M : Ideal S) (p : S) :
    LinearMap.range (LinearMap.lsmul S (S ⧸ M) p) =
      Submodule.map (M : Submodule S S).mkQ (Ideal.span {p} : Submodule S S) := by
  ext x
  rw [LinearMap.mem_range, Submodule.mem_map]
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective M y
    refine ⟨p * z, Ideal.mul_mem_right z _ (Ideal.mem_span_singleton_self p), ?_⟩
    rw [LinearMap.lsmul_apply]
    exact (map_smul (M : Submodule S S).mkQ p z).symm
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hw
    refine ⟨Submodule.mkQ M r, ?_⟩
    rw [LinearMap.lsmul_apply, hr]
    exact (map_smul (M : Submodule S S).mkQ p r).symm

/-- `(S ⧸ M) ⧸ range (p ·)` and `S ⧸ (M ⊔ (p))` have the same length. -/
private theorem length_quot_range_lsmul {S : Type*} [CommRing S] (M : Ideal S) (p : S) :
    Module.length S ((S ⧸ M) ⧸ LinearMap.range (LinearMap.lsmul S (S ⧸ M) p)) =
      Module.length S (S ⧸ (M ⊔ Ideal.span {p})) := by
  rw [range_lsmul_eq M p]
  have h : Submodule.map (M : Submodule S S).mkQ (M ⊔ Ideal.span {p})
      = Submodule.map (M : Submodule S S).mkQ (Ideal.span {p}) := by
    rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]
  rw [← h]
  exact (Submodule.quotientQuotientEquivQuotient M (M ⊔ Ideal.span {p}) le_sup_left).length_eq

/-- Ring-level core: for ideals `a c` of a Noetherian ring and `p : S`,
`ℓ(S ⧸ ((a ⊓ c) ⊔ (p))) ≤ ℓ(S ⧸ (a ⊔ (p))) + ℓ(S ⧸ (c ⊔ (p)))` in `ℕ∞`. -/
private theorem length_sup_inf_span_le_aux {S : Type*} [CommRing S] [IsNoetherianRing S]
    (a c : Ideal S) (p : S) :
    Module.length S (S ⧸ ((a ⊓ c) ⊔ Ideal.span {p})) ≤
      Module.length S (S ⧸ (a ⊔ Ideal.span {p})) +
        Module.length S (S ⧸ (c ⊔ Ideal.span {p})) := by
  have h1 := Work.BW.RB.length_cut_kernel_le_tor a c p
  have h2 := Work.BW.RB.length_ker_lsmul_le_quot (S := S) (N := S ⧸ (a ⊔ c)) p
  have h3 := length_quot_range_lsmul (a ⊔ c) p
  have hmv := mv_length (a ⊔ Ideal.span {p}) (c ⊔ Ideal.span {p})
  have hsup : (a ⊔ Ideal.span {p}) ⊔ (c ⊔ Ideal.span {p}) = (a ⊔ c) ⊔ Ideal.span {p} := by
    ac_rfl
  calc Module.length S (S ⧸ ((a ⊓ c) ⊔ Ideal.span {p}))
      ≤ Module.length S (S ⧸ ((a ⊔ Ideal.span {p}) ⊓ (c ⊔ Ideal.span {p})))
          + Module.length S (LinearMap.ker (LinearMap.lsmul S (S ⧸ (a ⊔ c)) p)) := h1
    _ ≤ Module.length S (S ⧸ ((a ⊔ Ideal.span {p}) ⊓ (c ⊔ Ideal.span {p})))
          + Module.length S (S ⧸ ((a ⊔ c) ⊔ Ideal.span {p})) :=
          add_le_add le_rfl (h2.trans (le_of_eq h3))
    _ = Module.length S (S ⧸ (a ⊔ Ideal.span {p}))
          + Module.length S (S ⧸ (c ⊔ Ideal.span {p})) := by
          rw [← hsup]; exact hmv

/-- Corrected form of the local principal-cut subadditivity: identical to the statement in
`RB/locLenAt_sup_inf_le_loc.lean` plus `[IsNoetherianRing R]`. Without Noetherianity the
inequality is false (see VERDICT.md, idealization counterexample). `hfin` is kept only so that
the call site in `finset_inf_sup_le_sum` is unchanged; the proof does not need it.
Proof: localize (`IsLocalization.map_inf`, `Ideal.map_sup`, `Ideal.map_span`), `R_q` is
Noetherian, then apply `length_sup_inf_span_le` in `S = R_q`. -/
theorem locLenAt_sup_inf_le_loc {R : Type*} [CommRing R] [IsNoetherianRing R]
    (A C : Ideal R) (P : R) (q : Ideal R) (hq : q.IsPrime)
    (hfin : Work.BW.locLenAt q hq ((A ⊓ C) ⊔ Ideal.span {P}) ≠ ⊤) :
    Work.BW.locLenAt q hq ((A ⊓ C) ⊔ Ideal.span {P}) ≤
      Work.BW.locLenAt q hq (A ⊔ Ideal.span {P}) +
        Work.BW.locLenAt q hq (C ⊔ Ideal.span {P}) := by
  -- Unfold `locLenAt` and reduce to the ring-level statement in `S = R_q`.
  letI := hq
  have key : ∀ J : Ideal R, Work.BW.locLenAt q hq J =
      Module.length (Localization.AtPrime q)
        (Localization.AtPrime q ⧸ J.map (algebraMap R (Localization.AtPrime q))) := fun J => rfl
  rw [key ((A ⊓ C) ⊔ Ideal.span {P}), key (A ⊔ Ideal.span {P}), key (C ⊔ Ideal.span {P})]
  have hL : ((A ⊓ C) ⊔ Ideal.span {P}).map (algebraMap R (Localization.AtPrime q)) =
      (A.map (algebraMap R (Localization.AtPrime q)) ⊓
        C.map (algebraMap R (Localization.AtPrime q))) ⊔
        Ideal.span {(algebraMap R (Localization.AtPrime q)) P} := by
    rw [Ideal.map_sup, IsLocalization.map_inf q.primeCompl _ A C, Ideal.map_span,
      Set.image_singleton]
  have hA : (A ⊔ Ideal.span {P}).map (algebraMap R (Localization.AtPrime q)) =
      A.map (algebraMap R (Localization.AtPrime q)) ⊔
        Ideal.span {(algebraMap R (Localization.AtPrime q)) P} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have hC : (C ⊔ Ideal.span {P}).map (algebraMap R (Localization.AtPrime q)) =
      C.map (algebraMap R (Localization.AtPrime q)) ⊔
        Ideal.span {(algebraMap R (Localization.AtPrime q)) P} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  rw [hL, hA, hC]
  exact length_sup_inf_span_le_aux _ _ _


end Work.BW.RB
