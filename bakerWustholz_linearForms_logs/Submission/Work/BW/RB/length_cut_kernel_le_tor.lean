import Mathlib
import Submission.Work.BW.BWGradedBase
import Submission.Work.BW.colon_localize_length_add

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

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

/-- Any commutative ring. The kernel `K = ((a+(p))⊓(c+(p)))/((a⊓c)+(p))` of the surjection
`S/((a⊓c)+(p)) → S/((a+(p))⊓(c+(p)))` has length at most that of the `p`-torsion of `S/(a⊔c)`.
Proof: `length_eq_add_of_exact` for `0 → K → S/((a⊓c)+(p)) → S/((a+(p))⊓(c+(p))) → 0` reduces
to `ℓ(K) ≤ ℓ(tor)`. Let `W = {(a₁, c₁, t) ∈ a × c × S | c₁ - a₁ = t * p}` (a submodule of
`a × c × S`). `h : W → K`, `(a₁,c₁,t) ↦ [c₁]` is surjective: for `x = a₀ + r p = c₀ + s p` take
`(a₀, c₀, r - s)`, and `[c₀] = [x - s p] = [x]`. `g : W → tor`, `(a₁,c₁,t) ↦ [t]` lands in the
torsion since `t p = c₁ - a₁ ∈ a ⊔ c`. `ker g ≤ ker h`: if `t = u + v`, `u ∈ a`, `v ∈ c`, then
`c₁ - v p = a₁ + u p ∈ a ⊓ c`, so `c₁ ∈ (a⊓c) + (p)`. Hence `h` factors through
`W ⧸ ker g ≃ range g ≤ tor`, giving `ℓ(K) ≤ ℓ(W ⧸ ker g) ≤ ℓ(tor)`. -/
theorem length_cut_kernel_le_tor {S : Type*} [CommRing S] (a c : Ideal S) (p : S) :
    Module.length S (S ⧸ ((a ⊓ c) ⊔ Ideal.span {p})) ≤
      Module.length S (S ⧸ ((a ⊔ Ideal.span {p}) ⊓ (c ⊔ Ideal.span {p}))) +
        Module.length S (LinearMap.ker (LinearMap.lsmul S (S ⧸ (a ⊔ c)) p)) := by
  -- The kernel of `S ⧸ I → S ⧸ J`, where `I = (a ⊓ c) ⊔ (p)` and `J = (a ⊔ (p)) ⊓ (c ⊔ (p))`.
  set I : Ideal S := (a ⊓ c) ⊔ Ideal.span {p} with hI
  set J : Ideal S := (a ⊔ Ideal.span {p}) ⊓ (c ⊔ Ideal.span {p}) with hJ
  have hIJ : I ≤ J := by
    rw [hI, hJ]
    exact le_inf (sup_le (le_trans inf_le_left le_sup_left) le_sup_right)
      (sup_le (le_trans inf_le_right le_sup_left) le_sup_right)
  -- The submodule `W = {(a₁, c₁, t) ∈ a × c × S | c₁ - a₁ = t * p}`.
  let prA : (↥a × ↥c) × S →ₗ[S] ↥a :=
    (LinearMap.fst S ↥a ↥c).comp (LinearMap.fst S (↥a × ↥c) S)
  let prC : (↥a × ↥c) × S →ₗ[S] ↥c :=
    (LinearMap.snd S ↥a ↥c).comp (LinearMap.fst S (↥a × ↥c) S)
  let prS : (↥a × ↥c) × S →ₗ[S] S := LinearMap.snd S (↥a × ↥c) S
  let φ : (↥a × ↥c) × S →ₗ[S] S :=
    ((c : Submodule S S).subtype.comp prC) - ((a : Submodule S S).subtype.comp prA) -
      ((LinearMap.mulRight S p).comp prS)
  let W : Submodule S ((↥a × ↥c) × S) := LinearMap.ker φ
  -- `h : W → S ⧸ I`, `(a₁, c₁, t) ↦ [c₁]`.
  let H0 : (↥a × ↥c) × S →ₗ[S] S ⧸ I :=
    (Submodule.mkQ (I : Submodule S S)).comp ((c : Submodule S S).subtype.comp prC)
  let h : W →ₗ[S] S ⧸ I := H0.comp W.subtype
  -- `g : W → S ⧸ (a ⊔ c)`, `(a₁, c₁, t) ↦ [t]`.
  let G0 : (↥a × ↥c) × S →ₗ[S] S ⧸ (a ⊔ c) :=
    (Submodule.mkQ ((a ⊔ c) : Submodule S S)).comp prS
  let gRaw : W →ₗ[S] S ⧸ (a ⊔ c) := G0.comp W.subtype
  let tor : Submodule S (S ⧸ (a ⊔ c)) := LinearMap.ker (LinearMap.lsmul S (S ⧸ (a ⊔ c)) p)
  -- Description of `W` and of the two maps on its elements.
  have key : ∀ (a1 : ↥a) (c1 : ↥c) (t : S),
      (⟨⟨a1, c1⟩, t⟩ : (↥a × ↥c) × S) ∈ W ↔ (c1 : S) - (a1 : S) = t * p := by
    intro a1 c1 t
    simp only [W, LinearMap.mem_ker, φ, prA, prC, prS, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.mulRight_apply, Submodule.subtype_apply]
    constructor
    · intro hh; linear_combination hh
    · intro hh; rw [hh]; ring
  have h_apply : ∀ (a1 : ↥a) (c1 : ↥c) (t : S)
      (hw : (⟨⟨a1, c1⟩, t⟩ : (↥a × ↥c) × S) ∈ W),
      h ⟨⟨⟨a1, c1⟩, t⟩, hw⟩ = Submodule.Quotient.mk (c1 : S) := by
    intro a1 c1 t hw; rfl
  have g_apply : ∀ (a1 : ↥a) (c1 : ↥c) (t : S)
      (hw : (⟨⟨a1, c1⟩, t⟩ : (↥a × ↥c) × S) ∈ W),
      gRaw ⟨⟨⟨a1, c1⟩, t⟩, hw⟩ = Submodule.Quotient.mk t := by
    intro a1 c1 t hw; rfl
  -- `g` lands in the `p`-torsion of `S ⧸ (a ⊔ c)`: `t * p = c₁ - a₁ ∈ a ⊔ c`.
  have gmem : ∀ w : W, gRaw w ∈ tor := by
    intro w
    obtain ⟨⟨⟨a1, c1⟩, t⟩, hw⟩ := w
    simp only [tor, LinearMap.mem_ker, LinearMap.lsmul_apply, g_apply a1 c1 t hw,
      ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    have hrel := (key a1 c1 t).mp hw
    have hpt : (p • t : S) = (c1 : S) - (a1 : S) := by
      rw [smul_eq_mul, hrel]; ring
    rw [hpt]
    exact Submodule.sub_mem (a ⊔ c) (SetLike.le_def.mp le_sup_right c1.2)
      (SetLike.le_def.mp le_sup_left a1.2)
  let g : W →ₗ[S] ↥tor := gRaw.codRestrict tor gmem
  -- `h` factors through the kernel of `S ⧸ I → S ⧸ J`.
  have hmem : ∀ w : W, h w ∈ LinearMap.ker (Submodule.factor hIJ) := by
    intro w
    obtain ⟨⟨⟨a1, c1⟩, t⟩, hw⟩ := w
    rw [LinearMap.mem_ker, h_apply a1 c1 t hw, Submodule.factor, Submodule.mapQ_apply]
    simp only [LinearMap.id_apply]
    rw [Submodule.Quotient.mk_eq_zero, hJ]
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · have hrel := (key a1 c1 t).mp hw
      have heq : (c1 : S) = (a1 : S) + t * p := by linear_combination hrel
      rw [heq]
      exact Submodule.mem_sup.mpr ⟨a1, a1.2, t * p,
        Submodule.mem_span_singleton.mpr ⟨t, rfl⟩, rfl⟩
    · exact SetLike.le_def.mp le_sup_left c1.2
  let Φ : W →ₗ[S] ↥(LinearMap.ker (Submodule.factor hIJ)) := h.codRestrict _ hmem
  -- Surjectivity of `h` onto that kernel.
  have hrange : h.range = LinearMap.ker (Submodule.factor hIJ) := by
    apply le_antisymm
    · rintro z ⟨w, rfl⟩
      exact hmem w
    · intro z hz
      rw [LinearMap.mem_ker] at hz
      rw [LinearMap.mem_range]
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I : Submodule S S) z
      rw [Submodule.factor_mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
      rw [hJ] at hz
      obtain ⟨hxa, hxc⟩ := Submodule.mem_inf.mp hz
      obtain ⟨y1, hy1, z1, hz1, hy1z1⟩ := Submodule.mem_sup.mp hxa
      obtain ⟨y2, hy2, z2, hz2, hy2z2⟩ := Submodule.mem_sup.mp hxc
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hz1
      obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hz2
      have hr' : r * p = z1 := by simpa using hr
      have hs' : s * p = z2 := by simpa using hs
      have h1 : (y1 : S) + r * p = x := by rw [← hr'] at hy1z1; exact hy1z1
      have h2 : (y2 : S) + s * p = x := by rw [← hs'] at hy2z2; exact hy2z2
      have hrel : (y2 : S) - (y1 : S) = (r - s) * p := by linear_combination h2 - h1
      refine ⟨⟨⟨⟨⟨y1, hy1⟩, ⟨y2, hy2⟩⟩, r - s⟩,
        (key ⟨y1, hy1⟩ ⟨y2, hy2⟩ (r - s)).mpr hrel⟩, ?_⟩
      rw [h_apply ⟨y1, hy1⟩ ⟨y2, hy2⟩ (r - s) _]
      rw [Submodule.mkQ_apply, Submodule.Quotient.eq]
      have hyx : (y2 : S) - x = -(s * p) := by linear_combination h2
      rw [hyx]
      exact Submodule.neg_mem _ (SetLike.le_def.mp le_sup_right
        (Submodule.mem_span_singleton.mpr ⟨s, rfl⟩))
  have hsurj : Function.Surjective Φ := by
    intro z
    have hz : z.1 ∈ h.range := by rw [hrange]; exact z.2
    obtain ⟨w, hw⟩ := hz
    exact ⟨w, Subtype.ext (by simpa [Φ] using hw)⟩
  -- `ker g ≤ ker h`: if `t = u + v` with `u ∈ a`, `v ∈ c`, then `c₁ - v * p = a₁ + u * p ∈ a ⊓ c`.
  have hkg : g.ker ≤ Φ.ker := by
    intro w hw
    obtain ⟨⟨⟨a1, c1⟩, t⟩, hW⟩ := w
    rw [LinearMap.mem_ker] at hw ⊢
    have hgw : gRaw ⟨⟨⟨a1, c1⟩, t⟩, hW⟩ = 0 := by
      have h2 : ((g ⟨⟨⟨a1, c1⟩, t⟩, hW⟩ : ↥tor) : S ⧸ (a ⊔ c)) = 0 := congrArg Subtype.val hw
      simpa [g] using h2
    rw [g_apply a1 c1 t hW, Submodule.Quotient.mk_eq_zero] at hgw
    have hh0 : h ⟨⟨⟨a1, c1⟩, t⟩, hW⟩ = 0 := by
      rw [h_apply a1 c1 t hW, Submodule.Quotient.mk_eq_zero, hI]
      obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hgw
      have hrel := (key a1 c1 t).mp hW
      have htp : t * p = u * p + v * p := by rw [← huv]; ring
      have hkey : (c1 : S) - v * p = (a1 : S) + u * p := by
        have hc1 : (c1 : S) = (a1 : S) + t * p := by linear_combination hrel
        rw [hc1, htp]; ring
      have hmeminf : (a1 : S) + u * p ∈ (a ⊓ c : Ideal S) := by
        refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
        · exact Submodule.add_mem (a : Submodule S S) a1.2
            (by simpa [mul_comm] using Submodule.smul_mem (a : Submodule S S) p hu)
        · rw [← hkey]
          exact Submodule.sub_mem (c : Submodule S S) c1.2
            (by simpa [mul_comm] using Submodule.smul_mem (c : Submodule S S) p hv)
      refine Submodule.mem_sup.mpr ⟨(a1 : S) + u * p, hmeminf, v * p,
        Submodule.mem_span_singleton.mpr ⟨v, rfl⟩, ?_⟩
      rw [← hkey]; ring
    apply Subtype.ext
    simpa [Φ] using hh0
  -- `ℓ(S ⧸ I) = ℓ(S ⧸ J) + ℓ(K)` for `K = ker (S ⧸ I → S ⧸ J)`.
  have hlen : Module.length S (S ⧸ I) =
      Module.length S (S ⧸ J) +
        Module.length S ↥(LinearMap.ker (Submodule.factor hIJ)) := by
    have h0 : Module.length S (S ⧸ I) =
        Module.length S ↥(LinearMap.ker (Submodule.factor hIJ)) + Module.length S (S ⧸ J) :=
      Module.length_eq_add_of_exact (LinearMap.ker (Submodule.factor hIJ)).subtype
        (Submodule.factor hIJ) (Submodule.subtype_injective _) (Submodule.factor_surjective hIJ)
        (LinearMap.exact_subtype_ker_map _)
    rw [h0, add_comm]
  have heqΦ : Module.length S (W ⧸ Φ.ker) =
      Module.length S ↥Φ.range := LinearEquiv.length_eq (LinearMap.quotKerEquivRange Φ)
  have h2 : Module.length S ↥(LinearMap.ker (Submodule.factor hIJ)) =
      Module.length S (W ⧸ Φ.ker) := by
    rw [heqΦ, LinearMap.range_eq_top.mpr hsurj, Module.length_top]
  have h3 : Module.length S (W ⧸ Φ.ker) ≤ Module.length S (W ⧸ g.ker) :=
    Module.length_le_of_surjective (Submodule.factor hkg) (Submodule.factor_surjective hkg)
  have heqg : Module.length S (W ⧸ g.ker) = Module.length S ↥g.range :=
    LinearEquiv.length_eq (LinearMap.quotKerEquivRange g)
  have h4 : Module.length S (W ⧸ g.ker) ≤ Module.length S ↥tor :=
    le_trans (le_of_eq heqg)
      (Module.length_le_of_injective (Submodule.subtype g.range) (Submodule.subtype_injective g.range))
  have h5 : Module.length S ↥(LinearMap.ker (Submodule.factor hIJ)) ≤ Module.length S ↥tor := by
    rw [h2]; exact le_trans h3 h4
  rw [hlen]
  exact add_le_add_right h5 _


end Work.BW.RB
