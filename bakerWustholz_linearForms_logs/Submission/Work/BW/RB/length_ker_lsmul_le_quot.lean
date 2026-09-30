import Mathlib
import Submission.Work.BW.BWGradedBase
import Submission.Work.BW.colon_localize_length_add
import Submission.Work.BW.RB.nilpotent_length_ker_le_quot

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

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

/-- For a Noetherian module `N` and `x ∈ S`, `ℓ(ker (x • ·)) ≤ ℓ(N / xN)` in `ℕ∞`
(false for non-Noetherian `N`, e.g. the Prüfer module over a DVR).
Proof: if `ℓ(N/xN) = ⊤` trivial. The chain `ker (x^n •)` stabilizes (`IsNoetherian`,
`monotone_stabilizes`) at `n`; `T := ker (x^n •)`. (i) `ker (x •) ≤ T` and equals
`ker (x •)|_T`. (ii) `T ⧸ xT → N ⧸ xN` is injective: `t = x m`, `t ∈ T` gives
`m ∈ ker x^(n+1) = T`. (iii) `T` has finite length: `x^n T = 0` and each `x^i T / x^(i+1) T` is
the image of `T/xT` under `x^i`, so `ℓ(T) ≤ n · ℓ(T/xT)`. (iv) On finite-length `T`,
`ℓ(T) = ℓ(ker) + ℓ(xT) = ℓ(xT) + ℓ(T/xT)` gives `ℓ(ker) = ℓ(T/xT) ≤ ℓ(N/xN)`. -/
theorem length_ker_lsmul_le_quot {S N : Type*} [CommRing S] [AddCommGroup N] [Module S N]
    [IsNoetherian S N] (x : S) :
    Module.length S (LinearMap.ker (LinearMap.lsmul S N x)) ≤
      Module.length S (N ⧸ LinearMap.range (LinearMap.lsmul S N x)) := by
  set f : N →ₗ[S] N := LinearMap.lsmul S N x with hf
  obtain ⟨n₀, hn₀⟩ :=
    (monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian S N)) f.iterateKer
  set n : ℕ := n₀ + 1 with hn_def
  have hn1 : 1 ≤ n := by omega
  have hstab : f.iterateKer n = f.iterateKer (n + 1) := by
    have h1 : f.iterateKer n₀ = f.iterateKer n := hn₀ n (by omega)
    have h2 : f.iterateKer n₀ = f.iterateKer (n + 1) := hn₀ (n + 1) (by omega)
    rw [← h1, h2]
  set T : Submodule S N := LinearMap.ker (f ^ n) with hT
  have hstabk : LinearMap.ker (f ^ (n + 1)) = T := by
    rw [← LinearMap.iterateKer_coe f (n + 1), ← hstab, LinearMap.iterateKer_coe f n, hT]
  have hmemT : ∀ y : N, y ∈ T ↔ (f ^ n) y = 0 := by
    intro y; rw [hT, LinearMap.mem_ker]
  have hK_le_T : LinearMap.ker f ≤ T := by
    have h := f.iterateKer.monotone hn1
    simp only [LinearMap.iterateKer_coe, pow_one] at h
    rwa [hT]
  have hstabmap : ∀ t ∈ T, f t ∈ T := by
    intro t ht
    rw [hmemT] at ht ⊢
    rw [show (f ^ n) (f t) = (f ^ (n + 1)) t from by
          rw [← Module.End.mul_apply, ← pow_succ],
        pow_succ', Module.End.mul_apply, ht, map_zero]
  set g : T →ₗ[S] T := f.restrict hstabmap with hg_def
  have hg_apply : ∀ t : T, (g t : N) = f (t : N) := by
    intro t
    rw [hg_def]
    exact congrArg Subtype.val (LinearMap.restrict_apply hstabmap t)
  have hg_pow : ∀ k : ℕ, ∀ t : T, ((g ^ k) t : N) = (f ^ k) (t : N) := by
    intro k
    induction k with
    | zero => intro t; simp
    | succ k ih =>
      intro t
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih (g t), hg_apply t]
  have hgn : g ^ n = 0 := by
    ext t
    show ((g ^ n) t : N) = ((0 : T →ₗ[S] T) t : N)
    rw [LinearMap.zero_apply, hg_pow n t]
    exact (hmemT t).mp t.2
  have hstep1 : Module.length S (LinearMap.ker g) ≤ Module.length S (T ⧸ LinearMap.range g) :=
    nilpotent_length_ker_le_quot g n hgn
  have hker_eq : LinearMap.ker g = (LinearMap.ker f).comap T.subtype := by
    ext t
    rw [LinearMap.mem_ker, Submodule.mem_comap, LinearMap.mem_ker]
    constructor
    · intro h
      have : (g t : N) = 0 := by rw [h]; rfl
      rwa [hg_apply] at this
    · intro h
      apply Subtype.ext
      rw [hg_apply]
      exact h
  have hkn : Module.length S (LinearMap.ker g) = Module.length S (LinearMap.ker f) := by
    rw [hker_eq]
    exact (Submodule.comapSubtypeEquivOfLe hK_le_T).length_eq
  let A : Submodule S T := (LinearMap.range f).comap T.subtype
  have hA_eq : A = LinearMap.range g := by
    apply le_antisymm
    · intro y hy
      rw [Submodule.mem_comap] at hy
      rw [LinearMap.mem_range] at hy
      obtain ⟨m, hm⟩ := hy
      have hx0 : (f ^ n) (y : N) = 0 := (hmemT y).mp y.2
      have hmT : m ∈ T := by
        rw [← hstabk, LinearMap.mem_ker]
        rw [pow_succ, Module.End.mul_apply, hm]
        exact hx0
      refine ⟨⟨m, hmT⟩, ?_⟩
      apply Subtype.ext
      rw [hg_apply]
      exact hm
    · rintro y ⟨z, rfl⟩
      rw [Submodule.mem_comap]
      change (g z : N) ∈ f.range
      rw [hg_apply]
      exact LinearMap.mem_range_self f (z : N)
  have hstep2 : Module.length S (T ⧸ LinearMap.range g) ≤ Module.length S (T ⧸ A) := by
    rw [hA_eq]
  have hstep3 : Module.length S (T ⧸ A) ≤ Module.length S (N ⧸ LinearMap.range f) := by
    let ψ : T →ₗ[S] N ⧸ LinearMap.range f := (LinearMap.range f).mkQ.comp T.subtype
    have hkerψ : LinearMap.ker ψ = A := by
      ext y
      rw [LinearMap.mem_ker, Submodule.mem_comap]
      change ((LinearMap.range f).mkQ (T.subtype y) = 0) ↔ (T.subtype y ∈ LinearMap.range f)
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have hle : A ≤ LinearMap.ker ψ := le_of_eq hkerψ.symm
    have hinj : Function.Injective (A.liftQ ψ hle) := by
      rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot A ψ hle (le_of_eq hkerψ)
    exact Module.length_le_of_injective _ hinj
  calc Module.length S (LinearMap.ker f)
      = Module.length S (LinearMap.ker g) := hkn.symm
    _ ≤ Module.length S (T ⧸ LinearMap.range g) := hstep1
    _ ≤ Module.length S (T ⧸ A) := hstep2
    _ ≤ Module.length S (N ⧸ LinearMap.range f) := hstep3

end Work.BW.RB
