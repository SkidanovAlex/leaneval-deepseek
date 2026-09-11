import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.Analysis.Complex.ExponentialBounds
import ChallengeDeps
import Submission.SelCore
import Submission.Deep
import Submission.ObsTPrime
import Submission.ProfileSum
import Submission.Multi
import Submission.MultiDeep
import Submission.MultiDeep2
import Submission.MultiFrag1
import Submission.MultiFrag2
import Submission.MultiMass
import Submission.MultiZ

/-!
# TASK (child): prove `Submission.Multi.MSys.theorem_MLM` below (the multiset ML bound).
No unfinished proof (no `sor-ry`) may remain in the file at the end.

## SETTING
M := K*N, where K := 10^70 is a FIXED constant (define `noncomputable def Kbig : ℕ := 10^70`
and use it; the final theorem will be instantiated with N the number of i.i.d. samples, W a
random multiset of size M := Kbig*N with multinomial mass `mass M μ W`).
cost coefficient c := (Real.exp 1 : ℝ) * (N : ℝ)  (call it `eN`); wCost eN μ U =
∏_x (eN·μ x)^(U x)/(U x)!.
θ := (10:ℝ)^10 )⁻¹ is the BADNESS threshold.
BAD W means `N0.BadM θ W` = procValM N0 W < θ (procValM := mSup over N0.Fl of weightM).
`coverFinsetM N0 W hB` (min-fragment cover, in MultiDeep2.lean) and `coverCostM N0 eN μ W hB`
= mTotalCost eN μ (coverFinsetM ...)  (mTotalCost c p 𝓖 := ∑ G ∈ 𝓖, wCost c p G).

## THEOREM (keep exact name/signature):
theorem theorem_MLM (N : ℕ) (μ : X → ℝ) (N0 : MSys X)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμle : (∑ x : X, μ x) ≤ 1)
    (hB : N0.LevelBounded) (hTot : N0.TotBoundM) (hLeg : N0.FLegalM) :
    (∑ W ∈ (msizeExact (X := X) (Kbig * N)).filter (fun W => N0.BadM ((10 : ℝ) ^ 10)⁻¹ W),
        mass (X := X) (Kbig * N) μ W * coverCostM N0 ((Real.exp 1 : ℝ) * (N : ℝ)) μ W hB)
      ≤ (1 / 10 : ℝ)

## PROOF PLAN (read the paper pp. 880-940 of /tmp/Talagrand_final.tex — file may be readable —
and mirror Submission/ML.lean's structure, which did the identical argument for sets with
binomial mass; the multiset changes: W ranges over multisets of exact size M := Kbig·N with
mass M μ W; the covers use min-fragments of the multiset MSys N0 (all the fragment machinery
exists and is PROVEN: Submission/MultiFrag1.lean obsTM/obsMaxM/level_le_b_of_minFragM/
minFragM_subM_prefixM/t_le_nbM etc. and Submission/MultiFrag2.lean nb_le_tM); the "pairs"
(W, U ∈ coverFinsetM N0 W hB) are grouped by keys (b, s, t) exactly as ML.lean's groupKey/
fiber/keySet; the final Z-side bound uses Submission/MultiZ.lean mass_mul_cost_eq and
Submission/MultiMass.lean mass_sum_le_one, and the tail bound uses
Submission/ProfileSum.lean profile_sum_bound (ζ ∈ [0, 10⁻⁹], keys must satisfy hKb/hKleg/
hKtop/hKzero)).  Do NOT import Mathlib wholesale (keep file imports).

### STAGE 0 (setup; mirror ML.lean lines 34-160 / 380-580):
- Define pairSet: Finset ((X → ℕ) × (X → ℕ)) := product of the bad-multiset finset with
  (N0.Fl.image (fun S => N0.minFragM ...)) hmm: coverFinsetM N0 W hB is already a Finset;
  the product is over W ∈ badMsets × U ∈ coverFinsetM N0 W hB: since the second component
  depends on W, follow ML.lean: use the Finset of all pairs (W,U) with W bad and U in the
  Finset (msizeExact (Kbig*N) filtered bad) × (N0.Fl.image (fun S => N0.minFragM S W hS hB))
  — but the second set depends on W; ML.lean handled this via product with Finset.univ (Set X)
  and filter.  For multisets we CANNOT use Finset.univ over (X → ℕ).  Instead: define
  pairSet as the image of the Finset
    (badMsets).product (N0.Fl) under (fun (W,S) => (W, N0.minFragM S W hS hB))
  (each pair (W,U) with U = minFragM of some S; duplicates possible — fine for ≤ bounds since
  we only ever need the LHS ≤ Σ over pairs with positive coefficients... CAREFUL: LHS counts
  each U ∈ coverFinsetM (a Finset with multiplicities by construction via image: coverFinsetM
  is an image so duplicates collapsed!  ML.lean also had this issue and treated totalCost over
  the cover as a sum over the cover's elements — duplicates matter.  RESOLUTION used by ML:
  they SUMMED over pairs (W, U ∈ coverFinset) treating the cover as a set of distinct U, and
  the identity lhs = pairSum held because totalCost sums over the Finset coverFinset which
  itself is an image (distinct).  So in your pairSet use U ranging over the distinct members
  of coverFinsetM N0 W hB: representable as the Finset image in the product: define pairSet as
  (badMsets).bind (fun W => (coverFinsetM N0 W hB).image (fun U => (W,U))) — Finset.bind keeps
  distinct (W,U) pairs.  Use Finset.bind (see ML.lean? it used product over univ — for us
  bind is natural).  Then LHS = ∑ x ∈ pairSet, mass (sizeM x.1) μ x.1 * wCost eN μ x.2 and
  coverCostM W = ∑ U ∈ coverFinsetM W, wCost: prove:
    lhs_eq_pairSum : (∑ W ∈ badMsets, mass M μ W · coverCostM N0 eN μ W hB)
        = ∑ x ∈ pairSet M N0 hB eN μ, mass M μ x.1 · wCost eN μ x.2   [Finset.bind/sum_bij]
- For each pair, recover the member S with U = minFragM S W and its witness S' ∈ FPartialM S b:
  coverFinsetM_cover / coverFinsetM membership (rcases (Finset.mem_image)) gives S ∈ N0.Fl with
  U = minFragM S W hS hB (or the dummy zero when hS fails — but hS : S ∈ N0.F is always true
  for S ∈ N0.Fl: when you get U from the image element S, hS holds by simpa; note coverFinsetM
  is built as N0.Fl.image with if hS ... — show the image value for S ∈ N0.Fl is exactly
  minFragM S W (by simp [hS])).  b := N0.MinIndexM S W hS hB; witness S' := Classical.choose
  of minFragM_isFragmentM (or better: N0.minFragM_isFragmentM gives ∃ S', IsFragmentM S W U b S').
- groupKey x := (b, s) where s := fun j => if j ≤ b then N0.sCount S' j else 0 (S' = witness);
  keyTotal k := ∑ j ∈ range (k.1 + 1), k.2 j  (= n_b);  t := sizeM x.2.
- Split the pair sum by keys and by t:
    ∑ x ∈ pairSet, mass·wCost = ∑ k, ∑ t ∈ (range (keyTotal k + 1))-ish, ∑ x ∈ fiber(k,t), ...
  where fiber(k,t) := pairs with groupKey = k ∧ sizeM x.2 = t.

### STAGE 1 (per pair structural facts, mirroring ML.lean PairFacts + MultiFrag1/2; PROVE
lemmas with the SAME content but for multisets — most already exist):
- t_le_nb : sizeM x.2 ≤ keyTotal (groupKey x)    [t_le_nbM with witness S']
- nb_le_t  : (9/10)·(keyTotal : ℝ) ≤ (sizeM x.2 : ℝ)   [nb_le_tM: needs hTot + hbad: pairs are
  BAD by construction + the pair's U is a min fragment of its S at index b]
- 0 < sizeM x.2  (from .9n_b ≤ t and s_b ≠ 0 and n_b ≥ 1) → t ≥ 1
- s_b ≠ 0: N0.sCount S' b ≠ 0   [port ML.lean Step0.sb_ne_zero: use badness + min-index
  minimality: if sCount S' b = 0 then show U is already a fragment at index b−1 (the weight
  inequality at b−1 vs b and prefix equality: use level-le-b: U lives in levels ≤ b but level b
  is EMPTY in S' since sCount S' b = 0 → all U-copies at levels ≤ b−1; mirror ML.lean's proof
  which used sCount_eq_zero_of_prefix + weightAbove_pred_eq: these exist analogously in the
  multiset world — write fresh multiset versions inside this file using our lemmas], n_b ≥ 1]
- b ≤ N0.τ, s j = 0 for j > b (by sOf), s legal at j ≤ b (FLegalM witness).

### STAGE 2 (the Z-side bound; the heart; paper lines ~900-935):
For fixed key k = (b, s) and t with ⌈0.9·n_b⌉ ≤ t ≤ n_b (n_b := keyTotal k):
  Claim Z-bound:  ∑ x ∈ fiber(k,t), mass M μ x.1 · wCost eN μ x.2
      ≤ (e/Kbig)^t · 2^(3·n_b) · (∑ Z ∈ msizeExact (M + t), mass (M+t) μ Z)   [real powers: use
      natural powers: (e/Kbig : ℝ)^t · (2:ℝ)^(3·n_b);  e := Real.exp 1]
  PROOF STEPS:
  a) For each pair x with U := x.2, S-witness, Z := addM x.1 U (sizeM Z = M+t):
     obsTM-like facts give (i) subM U (prefixM S' b) [minFragM_subM_prefixM], so U x ≤ Ŝ-prefix,
     (ii) for z ∈ X with 0 < U z: x.1 z < S' z (obsMaxM: W z < S' z).
     Let Ŝ(Z) be a chosen feasible member: from the pair, S' is feasible for Z (FeasibleM: it
     satisfies fragment1 with W+U = Z and the weight inequality) — hence EXISTS a feasible Ŝ(Z)
     for Z (e.g. pick via Classical.choose the witness of any pair with that Z).
  b) The map x ↦ (Z, U) is injective on fiber(k,t) (U determined by Z and U; W = Z−U since
     W + U = Z ⇒ W = subMM Z U).  So the fiber sum ≤ ∑ over distinct (Z,U) images.  The image
     pairs (Z, U) have U ⊆ prefixM Ŝ(Z) b and sizeM U = t.  [You may find it easier to prove
     the claimed bound directly by summing over Z ∈ msizeExact (M+t) the U's with U ⊆ prefixM
     Ŝ(Z) b, U of size t, and bounding mass M μ (subMM Z U)·wCost eN μ U ≤ mass (M+t) μ Z ·
     (e/Kbig)^t · ∏_z 2^(2·Ŝ z) — see (c); this works even though extra (Z,U) pairs appear,
     because all terms are ≥ 0.]
  c) For Z, U ⊆ prefixM Ŝ b: use mass_mul_cost_eq (MultiZ.lean) with T := U, M := M, t := t,
     c := eN = (Real.exp 1)·(N : ℝ):
       mass M μ (subMM Z U) · wCost eN μ U
         = mass (M+t) μ Z · (M!·(M+t)!⁻¹) · (eN)^t · ∏_x (choose (Z x) (U x) : ℝ)
     Bound the three factors:
       - M!·(M+t)!⁻¹ ≤ M^{-t} as reals [M := Kbig·N; prove (Nat.factorial M : ℝ) *
         (Nat.factorial (M+t) : ℝ)⁻¹ ≤ ((M:ℝ)^t)⁻¹ by showing M!·(M+t)!⁻¹ = 1/(∏_{i=1..t}
         (M+i))-ish: simpler: prove by induction on t: fact M!·(M+t)!⁻¹ ≤ M⁻¹^t? provide a
         helper lemma `fact_ratio_le (M t) : (Nat.factorial M : ℝ)*(Nat.factorial (M+t):ℝ)⁻¹
         ≤ ((M:ℝ)^t)⁻¹` by induction on t using factorial_succ and M ≤ M+i and positivity]
       - (eN)^t · M^{-t} = (eN/M)^t = (e/Kbig)^t  [M = Kbig·N: eN/M = e/Kbig; prove via field_simp]
       - ∏_x (choose (Z x) (U x) : ℝ) ≤ ∏_x (2:ℝ)^(2·Ŝ(Z) x) over x ∈ X... CAREFUL: only for x
         with U x > 0 does Z x < Ŝ x + U x hold (obsMaxM).  For general x, C(Zx,Ux) ≤ 2^{Zx} ≤ ...
         handle all x: if Ux = 0: C(Zx,0)=1 ≤ 2^{2Ŝx}?? if Ux=0 then also Zx = Wx: C(Zx,0) = 1:
         need 1 ≤ 2^{2Ŝx}: not guaranteed (Ŝx might be 0).  So instead SUMMING over U ⊆ prefix:
         ∏_x Σ_{ux=0}^{pref x} C(Zx,ux)·[ux ≤ ...] hmm.  USE THE PAPER'S ROUTE: first
         ∏_x C(Zx,Ux) ≤ ∏_x 2^{Zx} ≤ ...: no.  PAPER: C(Zx,Ux) ≤ C(Ŝx+Ux, Ux) ≤ 2^{Ŝx+Ux} ≤
         2^{2Ŝx} — for x with Ux > 0 (then Zx < Ŝx+Ux).  For Ux = 0: C(Zx,0) = 1 ≤ 2^{2Ŝx}
         would need Ŝx ≥ 1... fails.  BUT the paper's T ranges over T ⊆ ∨_{j≤b}Ŝ_j (T U is
         contained in the PREFIX of Ŝ up to b); for x with Ux>0, Ŝx ≥ Ux ≥ 1.  The ∏ over ALL x
         including Ux=0 is wrong; instead keep the per-U product only over its support, then
         the number of U's is ∏_{x}(prefixx+1) ≤ 2^{n_b} and each contributes ∏_{x:Ux>0}2^{2Ŝx}
         ≤ 2^{2n_b}: total ≤ 2^{3n_b}.  SO: show Σ_{U ⊆ prefixM Ŝ b} ∏_x C(Zx,Ux)
         ≤ 2^{2n_b}·(#U) ≤ 2^{2n_b}·2^{n_b} = 2^{3n_b}: where for each U, ∏_x C(Zx,Ux) ≤
         2^{2·n_b}: prove per x: C(Zx,Ux) ≤ 2^{2·prefx} (with prefx := prefixM Ŝ b x): if Ux=0:
         C(Zx,0)=1 ≤ 2^{2prefx} needs prefx ≥ 0 ✓ (2^0=1: 1 ≤ 1 OK when prefx = 0; in general
         1 ≤ 2^{2prefx} ✓ since 2^{even} ≥ 1); if Ux ≥ 1: obsMaxM (x.1 x < Ŝ x, i.e. W x < Ŝ x):
         Zx = Wx+Ux ≤ Ŝx+Ux−? (Wx ≤ Ŝx−1 since integer) → Zx ≤ Ŝx+Ux−1 < Ŝx+Ux → C(Zx,Ux) ≤
         C(Ŝx+Ux−1, Ux) ≤ 2^{Ŝx+Ux−1} ≤ 2^{2Ŝx}: and 2^{2Ŝx} ≤ 2^{2prefx}? Ŝx vs prefx: U ⊆
         prefix so Ux ≤ prefx and (Ux ≥ 1 ⇒ Ŝx ≥ 1 but Ŝx may exceed prefx: 2^{2Ŝx} could
         exceed 2^{2prefx}!).  RESOLVE: use the bound C(Zx,Ux) ≤ 2^{2·Ux} ≤ 2^{2·prefx}?? C(Zx,Ux)
         ≤ 2^{Zx} ≤ 2^{...} no: standard: C(Zx,Ux) ≤ 2^{Zx}: Zx ≤ Ŝx+Ux−1 ≤ 2Ux−1+...? not
         bounded by 2prefx.  PAPER's actual line: Σ_{T ⊆ ∨Ŝ_j} ∏ 2^{2Ŝ(x)}: they bound the
         PRODUCT by 2^{2n_b} where n_b := |∨_{j≤b}Ŝ_j| — the product over x ∈ ∨Ŝ_j of 2^{2Ŝx}
         equals 2^{2·(Σ_{x∈∨}Ŝx)} = 2^{2n_b} (Σ over the prefix multiset of Ŝx = n_b!).  So the
         product runs over x in the PREFIX support only and each U ⊆ prefix has its ∏_x 2^{2Ŝx}
         over x in the prefix ≤ the full prefix product = 2^{2n_b}, TIMES #U ≤ 2^{n_b}.  For x
         with Ux = 0 we do NOT put the factor 2^{2Ŝx} (equivalently factor 1): fine.
       IMPLEMENT: for the per-Z bound first show
         Σ_{U ⊆ prefixM Ŝ b, sizeM U = t} ∏_x (choose (Zx)(Ux):ℝ)
            ≤ 2^{3n_b} (real; natural-power exponent (3·n_b))
         by: per x with prefx := prefixM Ŝ b x:
           Σ_{u = 0}^{prefx} (if we also need sizeM = t: DROP the size constraint (≥)):
           Σ_{U ⊆ prefix} ∏_x C(Zx,Ux) ≤ ∏_x (Σ_{u=0}^{prefx} C(Zx,u)) and C(Zx,u) ≤ 2^{2prefx}?
           C(Zx,u) ≤ 2^{Zx} and Zx ≤ Ŝx+u−1 ≤ 2·prefx when u ≥ 1? (Ŝx ≤ ?; Ŝx vs prefx: x in
           prefix of Ŝ up to b: for such x, prefx = Ŝx·[lv ≤ b]: if lv x ≤ b: prefx = Ŝx:
           Zx ≤ Ŝx+u−1 = prefx+u−1 ≤ 2prefx−1 ≤ 2prefx? need u ≤ prefx ✓: Zx ≤ prefx+u−1 ≤
           2prefx−1; if lv x > b: Ux = 0 (U ⊆ prefix) so u = 0, C(Zx,0)=1 = 2^0 ≤ 2^{2·0}:
           so per x: C(Zx,u) ≤ 2^{2prefx} for all 0 ≤ u ≤ prefx: then Σ_{u ≤ prefx} C(Zx,u) ≤
           (prefx+1)·2^{2prefx} ≤ 2^{prefx}·2^{2prefx} = 2^{3prefx}: ∏_x 2^{3prefx} = 2^{3n_b}
           ✓ (using (prefx+1) ≤ 2^{prefx} — a helper: (a+1) ≤ 2^a for a ∈ ℕ).
         CAREFUL with x ∉ prefix support (prefx = 0): (prefx+1) = 1 = 2^0 ✓.
       [So you need helpers: choose_le_two_pow (a u : ℕ) : (a.choose u) ≤ 2^a (or a ≤ b →);
        add_one_le_two_pow (a : ℕ) : a + 1 ≤ 2^a; sum over u of C(Zx,u) ≤ 2^{2prefx+?}...]
     THEN: ∑_{Z ∈ msizeExact (M+t)} mass (M+t) μ Z · (e/Kbig)^t · 2^{3n_b}
         ≤ (e/Kbig)^t · 2^{3n_b}   [mass_sum_le_one with hμ0 hμle]
  d) Aggregate over t: for key k with n := keyTotal k:
       ∑ t, (e/Kbig)^t · 2^{3n} ≤ (n+1)·(e/Kbig)^{⌊0.9n⌋}·2^{3n} ≤ 2^n·(e/Kbig)^{n/2}·2^{3n}
     [t ≥ ⌈0.9 n⌉ ≥ n/2 when n ≥ 1: use t ≥ n/2 ⟹ (e/Kbig)^t ≤ (e/Kbig)^{⌊n/2⌋} ≤ √(e/Kbig)^n:
      prove: since t ≥ ⌈0.9n⌉ and n ≥ 1, t ≥ n/2 → t ≥ n/2: 2t ≥ n: (e/K)^t ≤ (e/K)^{n/2}:
      handle with sqrt: ((e/Kbig)^t ≤ √(e/Kbig)^n) — PROVE with natural exponents:
      ((e/Kbig)^t)^2 ≤ (e/Kbig)^n from 2t ≥ n and 0 ≤ e/K ≤ 1, then sqrt.  SIMPLER: pick
      the cruder bound 0.9n ≥ 1/2·n... use: t ≥ (1/2)n: since t is natural: t ≥ n - n/2...]
     →  per key ≤ (16·√(e/Kbig))^n := ζ^n.   Then Σ over keys ζ^{n_b} ≤ 1/10 by
       ProfileSum.profile_sum_bound (ζ := 16·√(e/Kbig)); prove ζ ∈ [0, (10^9)⁻¹] from Kbig =
       10^70: 16·√(e/10^70) ≤ 10^{-9}: use (Real.exp 1) ≤ 3 (#check Real.exp_one_le? else prove
       exp 1 ≤ 3 by norm_num [exp_le_exp]? provide helper: exp_one_le_three : Real.exp 1 ≤ 3),
       and √(a) monotone + norm_num for the powers.
  e) finally sum over keys ≤ 1/10: THEOREM.

### IMPORTANT LEAN PRACTICALITIES
- Real powers (e/Kbig)^t and 2^(3n) are NATURAL powers ((:ℝ) ^ t) — fine.
- √ is Real.sqrt (Mathlib imports give it).  e := Real.exp 1 (a ℝ≥0? no, ℝ).  Careful with
  coefficients: wCost's first argument in coverCostM must be the REAL c := (Real.exp 1)*(N:ℝ).
- Fractions like (9/10), (1/10) are ℝ.  For sums over Finset.product/bind use sum_bij or
  sum_bind as appropriate; DISTINCTNESS/duplicates: state everything as ≤-chains so duplicates
  in images only help (all terms ≥ 0: mass_nonneg, wCost_nonneg — but mass needs μ ≥ 0 and
  wCost needs c ≥ 0: eN ≥ 0 ✓).  Use `Finset.bind` with care or express pairSet as the image
  under an INJECTIVE map from (badMsets × N0.Fl) so sums match; show injectivity from
  minFragM-subM-sdiff facts? minFrag of different S may coincide (fine: pairs (W,S) are
  distinct and map to (W,U) possibly equal: NOT injective).  SAFEST: define pairSet :=
  (badMsets).bind (fun W => (coverFinsetM N0 W hB).image (fun U => (W,U))) and use
  Finset.sum_bind + sum_image lemmas; note coverFinsetM is itself an image so covers might
  omit nothing needed.  The identity lhs = pair-sum is exactly:
     ∑ W bad, mass W·(∑ U ∈ cover W, wCost U) = ∑ W bad, ∑ U ∈ cover W, mass W · wCost U
     = ∑ x ∈ bind..., (mass x.1 · wCost x.2)  [by sum_bind: rw [Finset.sum_bind]; congr per W
     with Finset.sum_image over the image map].  Since mass·wCost ≥ 0 duplicates in the W-side
     don't matter because coverFinsetM W is already distinct-valued.
- For "witness S' of the min fragment of S at W" use N0.minFragM_isFragmentM S W hS hB
  : ∃ S', N0.IsFragmentM S W (N0.minFragM S W hS hB) (N0.MinIndexM S W hS hB) S'.
- In the Z-side, you must pick Ŝ(Z) : a member of N0.F that is (Z,b,s,t)-feasible, EXISTING
  for Z that arise; for Z not arising from any pair just put Ŝ(Z) := a dummy member of N0.F
  (exists only if N0.Fl nonempty — handle empty family: then no bad W and sums are 0: prove
  the theorem first under N0.Fl.Nonempty or handle empty by a separate case: if N0.Fl = ∅ the
  LHS is 0 ≤ 1/10 trivially since badMsets empty: procValM of empty family is 0 < θ?? BadM =
  procValM < θ: with mSup empty = 0 < 10^{-10} TRUE: so ALL W bad... but coverFinsetM = ∅ so
  coverCost = 0: LHS = 0 ✓ trivial).  To choose Ŝ(Z) for ALL Z (including non-arising), when
  N0.Fl is empty the bound is trivial; otherwise pick a canonical member for dummy Z and the
  chosen feasible one for arising Z — or simply SUM only over arising Z by carrying the
  witness from the pair: cleaner: prove the per-(key,t) bound by SUMMING OVER PAIRS (not over
  all Z): keep pairs and map to Z but bound Σ_{pairs} ≤ Σ_{Z ∈ msizeExact(M+t)} (of the
  U-that-come-from-pairs with THAT Z) ≤ Σ_{Z} Σ_{U ∈ chosen U's for Z} ... where for each Z the
  feasible Ŝ(Z) exists because SOME pair with that Z exists: choose Ŝ(Z) := the witness of the
  first pair (by Classical.choose over an existential) — then for OTHER pairs with the same Z
  their U's ⊆ prefixM Ŝ(Z) b needs obsTM for the CHOSEN Ŝ(Z): obsTM says U = prefixM Ŝ b ∖ W
  for ANY feasible witness Ŝ of the min fragment?  YES: obsTM holds for the min-fragment U with
  ANY feasible S' (our MultiFrag1 statements are stated for an IsFragmentM witness hfr; and any
  feasible S' gives IsFragmentM via feasibility+U⊆S∖W: build such a lemma yourself:
  `feasible_of_minFrag_isFragmentM` (hmin + FeasibleM → IsFragmentM S W U b S') using
  U ⊆ subMM S W from hmin (its witness part) — then reuse obsTM/obsMaxM/minFragM_subM_prefixM
  with that.  So for each arising Z pick ONE (W₀,U₀) with Z and its S'₀; Ŝ(Z) := S'₀, and all
  U of pairs (W,U) with W+U=Z satisfy U ⊆ prefixM Ŝ b via obsTM for Ŝ (feasible).]
  Provide such glue lemmas at the top of the proof.

You may restructure freely but the final theorem name/signature must remain.  Keep the import
list as-is (no extra `import Mathlib`).  Namespace: Submission.Multi.MSys.  No sorries/axioms.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
open Classical
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace Multi

open Sel.Deep

variable {X : Type*} [Fintype X]

namespace MSys

/-- the cover cost with coefficient eN over the min-fragment cover of W -/
noncomputable def coverCostEN (N0 : MSys X) (N : ℕ) (μ : X → ℝ) (W : X → ℕ)
    (hB : N0.LevelBounded) : ℝ :=
  N0.coverCostM (eN N) μ W hB

/-- bad multisets of exact size M -/
noncomputable def badMsetsM (N0 : MSys X) (M : ℕ) : Finset (X → ℕ) :=
  (msizeExact (X := X) M).filter (fun W : X → ℕ => N0.BadM ((10 : ℝ) ^ 10)⁻¹ W)

/- the multiset ML bound (the multiset analogue of Submission/ML.lean theorem_ML) -/

/- ## Part 1: the multiset ML bound: pair machinery and Z-side -/

/-- rho := e / Kbig -/
noncomputable def rhoVal : ℝ := ee / (Kbig : ℝ)

/-- zeta := 2^3 · sqrt(rho) -/
noncomputable def zetaVal : ℝ := (2 : ℝ) ^ 3 * Real.sqrt rhoVal

/-- min fragment of (S,W) with the membership proof handled inside (0 if S ∉ F) -/
noncomputable def minFragMOf (N0 : MSys X) (W S : X → ℕ) (hB : N0.LevelBounded) : X → ℕ := by
  classical
  exact if hS : S ∈ N0.F then N0.minFragM S W hS hB else fun _ => 0

/-- min index of (S,W) with the membership proof handled inside (0 if S ∉ F) -/
noncomputable def minIndexMOf (N0 : MSys X) (W S : X → ℕ) (hB : N0.LevelBounded) : ℕ := by
  classical
  exact if hS : S ∈ N0.F then N0.MinIndexM S W hS hB else 0

/-- pair value: mass of W times cost of U -/
noncomputable def pairWeight (M : ℕ) (c : ℝ) (μ : X → ℝ) (x : (X → ℕ) × (X → ℕ)) : ℝ :=
  mass M μ x.1 * wCost c μ x.2

/-- the finset of pairs (W, U) with W bad of size M and U in the min-fragment cover of W -/
noncomputable def pairSet (N0 : MSys X) (M : ℕ) (hB : N0.LevelBounded) : Finset ((X → ℕ) × (X → ℕ)) :=
  (badMsetsM N0 M).biUnion (fun W => (N0.coverFinsetM W hB).image (fun U => (W, U)))

/-- membership in the cover gives a member of F with that minFrag -/
lemma coverFinsetM_mem_exists (N0 : MSys X) (W U : X → ℕ) (hB : N0.LevelBounded)
    (hU : U ∈ N0.coverFinsetM W hB) :
    ∃ S : X → ℕ, S ∈ N0.F ∧ N0.minFragMOf W S hB = U := by
  classical
  unfold coverFinsetM at hU
  rcases (Finset.mem_image.mp hU) with ⟨S, hSF, hS⟩
  refine ⟨S, ?_, ?_⟩
  · exact (Fl_mem_F (N := N0) hSF)
  · have hS' : S ∈ N0.F := (Fl_mem_F (N := N0) hSF)
    unfold minFragMOf
    rw [dif_pos hS']
    simpa [hS'] using hS

/-- chosen member of F realizing U as minFrag of W -/
noncomputable def witness (N0 : MSys X) (hB : N0.LevelBounded) (W U : X → ℕ) : X → ℕ := by
  classical
  exact if h : U ∈ N0.coverFinsetM W hB then Classical.choose (coverFinsetM_mem_exists N0 W U hB h)
    else fun _ => 0

lemma witness_mem (N0 : MSys X) (hB : N0.LevelBounded) (W U : X → ℕ)
    (hU : U ∈ N0.coverFinsetM W hB) : witness N0 hB W U ∈ N0.F := by
  classical
  unfold witness
  rw [dif_pos hU]
  exact (Classical.choose_spec (coverFinsetM_mem_exists N0 W U hB hU)).1

lemma witness_spec (N0 : MSys X) (hB : N0.LevelBounded) (W U : X → ℕ)
    (hU : U ∈ N0.coverFinsetM W hB) :
    N0.minFragMOf W (witness N0 hB W U) hB = U := by
  classical
  have hw : witness N0 hB W U = Classical.choose (coverFinsetM_mem_exists N0 W U hB hU) := by
    unfold witness
    rw [dif_pos hU]
  rcases (Classical.choose_spec (coverFinsetM_mem_exists N0 W U hB hU)) with ⟨hS, hsp⟩
  rw [hw]
  exact hsp

/-- minFragMOf agrees with minFragM when S ∈ F -/
lemma minFragMOf_eq_minFragM (N0 : MSys X) (W S : X → ℕ) (hB : N0.LevelBounded)
    (hS : S ∈ N0.F) : N0.minFragMOf W S hB = N0.minFragM S W hS hB := by
  unfold minFragMOf
  rw [dif_pos hS]

/-- membership of a pair -/
lemma mem_pairSet_iff (N0 : MSys X) (M : ℕ) (hB : N0.LevelBounded) (x : (X → ℕ) × (X → ℕ)) :
    x ∈ pairSet N0 M hB ↔ x.1 ∈ badMsetsM N0 M ∧ x.2 ∈ N0.coverFinsetM x.1 hB := by
  classical
  unfold pairSet
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨W, hW, hx⟩
    rw [Finset.mem_image] at hx
    rcases hx with ⟨U, hU, hx'⟩
    have hx1 : x.1 = W := congrArg Prod.fst hx'.symm
    have hx2 : x.2 = U := congrArg Prod.snd hx'.symm
    constructor
    · simpa [hx1] using hW
    · simpa [hx1, hx2] using hU
  · intro h
    refine ⟨x.1, h.1, ?_⟩
    rw [Finset.mem_image]
    exact ⟨x.2, h.2, rfl⟩

lemma pairSet_mem_bad {N0 : MSys X} {M : ℕ} {hB : N0.LevelBounded} {x : (X → ℕ) × (X → ℕ)}
    (hx : x ∈ pairSet N0 M hB) : x.1 ∈ badMsetsM N0 M := (mem_pairSet_iff N0 M hB x).mp hx |>.1

lemma pairSet_mem_cover {N0 : MSys X} {M : ℕ} {hB : N0.LevelBounded} {x : (X → ℕ) × (X → ℕ)}
    (hx : x ∈ pairSet N0 M hB) : x.2 ∈ N0.coverFinsetM x.1 hB :=
  (mem_pairSet_iff N0 M hB x).mp hx |>.2

lemma pair_mem_msizeExact {N0 : MSys X} {M : ℕ} {hB : N0.LevelBounded} {x : (X → ℕ) × (X → ℕ)}
    (hx : x ∈ pairSet N0 M hB) : x.1 ∈ msizeExact (X := X) M := by
  exact (Finset.mem_filter.mp (pairSet_mem_bad hx)).1

lemma pair_bad {N0 : MSys X} {M : ℕ} {hB : N0.LevelBounded} {x : (X → ℕ) × (X → ℕ)}
    (hx : x ∈ pairSet N0 M hB) : N0.BadM ((10 : ℝ) ^ 10)⁻¹ x.1 := by
  exact (Finset.mem_filter.mp (pairSet_mem_bad hx)).2

lemma pair_sizeM {N0 : MSys X} {M : ℕ} {hB : N0.LevelBounded} {x : (X → ℕ) × (X → ℕ)}
    (hx : x ∈ pairSet N0 M hB) : sizeM x.1 = M :=
  (mem_msizeExact_iff (X := X) (M := M)).mp (pair_mem_msizeExact hx)

/-- For a pair, its U is the minFrag of its chosen witness. -/
lemma pair_minFrag {N0 : MSys X} {M : ℕ} {hB : N0.LevelBounded} {x : (X → ℕ) × (X → ℕ)}
    (hx : x ∈ pairSet N0 M hB) :
    N0.minFragM (witness N0 hB x.1 x.2) x.1
      (witness_mem N0 hB x.1 x.2 (pairSet_mem_cover hx)) hB = x.2 := by
  have h1 := witness_spec N0 hB x.1 x.2 (pairSet_mem_cover hx)
  have h2 := minFragMOf_eq_minFragM N0 x.1 (witness N0 hB x.1 x.2) hB
    (witness_mem N0 hB x.1 x.2 (pairSet_mem_cover hx))
  rwa [h2] at h1

/-- key of a pair: (b, profile) with profile zero above b -/
noncomputable def bOf (N0 : MSys X) (hB : N0.LevelBounded) (x : (X → ℕ) × (X → ℕ)) : ℕ := by
  classical
  exact if h : x.2 ∈ N0.coverFinsetM x.1 hB then
    N0.MinIndexM (witness N0 hB x.1 x.2) x.1 (witness_mem N0 hB x.1 x.2 h) hB else 0

/-- zero-padded level-count function of the pair's witness -/
noncomputable def sOf (N0 : MSys X) (hB : N0.LevelBounded) (x : (X → ℕ) × (X → ℕ)) : ℕ → ℕ :=
  fun j => if j ≤ bOf N0 hB x then N0.sCount (witness N0 hB x.1 x.2) j else 0

/-- the full group key: (b, s) -/
noncomputable def groupKey (N0 : MSys X) (hB : N0.LevelBounded) (x : (X → ℕ) × (X → ℕ)) :
    ℕ × (ℕ → ℕ) := (bOf N0 hB x, sOf N0 hB x)

/-- fibers of groupKey inside pairSet -/
noncomputable def fiber (N0 : MSys X) (M : ℕ) (hB : N0.LevelBounded)
    (k : ℕ × (ℕ → ℕ)) : Finset ((X → ℕ) × (X → ℕ)) :=
  (pairSet N0 M hB).filter (fun x => groupKey N0 hB x = k)

/-- t-slice of a fiber -/
noncomputable def fiberT (N0 : MSys X) (M : ℕ) (hB : N0.LevelBounded)
    (k : ℕ × (ℕ → ℕ)) (t : ℕ) : Finset ((X → ℕ) × (X → ℕ)) :=
  (fiber N0 M hB k).filter (fun x => sizeM x.2 = t)

/-- n_b = sum of the counts up to the key's level -/
noncomputable def keyTotal (k : ℕ × (ℕ → ℕ)) : ℕ := ∑ j ∈ Finset.range (k.1 + 1), k.2 j

/-- the set of admissible t for a fiber key (independent of M) -/
noncomputable def fiberTs (k : ℕ × (ℕ → ℕ)) : Finset ℕ :=
  (Finset.range (keyTotal k + 1)).filter (fun t : ℕ => (9 / 10 : ℝ) * (keyTotal k : ℝ) ≤ (t : ℝ))

/-- sum of pair weights over pairs -/
noncomputable def pairSum (N0 : MSys X) (M : ℕ) (hB : N0.LevelBounded) (c : ℝ) (μ : X → ℝ) : ℝ :=
  ∑ x ∈ pairSet N0 M hB, mass M μ x.1 * wCost c μ x.2

/-- LHS equals the pair sum over pairSet -/
lemma lhs_eq_pairSum (N0 : MSys X) (M : ℕ) (hB : N0.LevelBounded) (c : ℝ) (μ : X → ℝ) :
    (∑ W ∈ badMsetsM N0 M, mass M μ W * (∑ U ∈ N0.coverFinsetM W hB, wCost c μ U)) =
      ∑ x ∈ pairSet N0 M hB, mass M μ x.1 * wCost c μ x.2 := by
  classical
  have hdisj : (↑(badMsetsM N0 M) : Set (X → ℕ)).PairwiseDisjoint
      (fun W => (N0.coverFinsetM W hB).image (fun U => (W, U))) := by
    intro W hW W' hW' hWW'
    change Disjoint ((N0.coverFinsetM W hB).image (fun U => (W, U)))
        ((N0.coverFinsetM W' hB).image (fun U => (W', U)))
    rw [Finset.disjoint_left]
    intro x hx hx'
    rcases (Finset.mem_image.mp hx) with ⟨U, hU, hx1⟩
    rcases (Finset.mem_image.mp hx') with ⟨U', hU', hx2⟩
    apply hWW'
    exact (congrArg Prod.fst hx1).trans (congrArg Prod.fst hx2).symm
  calc
    (∑ W ∈ badMsetsM N0 M, mass M μ W * (∑ U ∈ N0.coverFinsetM W hB, wCost c μ U))
        = ∑ W ∈ badMsetsM N0 M,
            ∑ U ∈ (N0.coverFinsetM W hB).image (fun U => (W, U)), mass M μ U.1 * wCost c μ U.2 := by
            apply Finset.sum_congr rfl
            intro W hW
            rw [Finset.mul_sum]
            have himg : (∑ U ∈ (N0.coverFinsetM W hB).image (fun U => (W, U)),
                  mass M μ U.1 * wCost c μ U.2)
                = ∑ U ∈ N0.coverFinsetM W hB, mass M μ (W, U).1 * wCost c μ (W, U).2 := by
              rw [Finset.sum_image]
              · intro u hu v hv huv
                exact congrArg Prod.snd huv
            rw [himg]
    _ = ∑ x ∈ (badMsetsM N0 M).biUnion
          (fun W => (N0.coverFinsetM W hB).image (fun U => (W, U))),
          mass M μ x.1 * wCost c μ x.2 := by
          rw [← Finset.sum_biUnion hdisj]
    _ = ∑ x ∈ pairSet N0 M hB, mass M μ x.1 * wCost c μ x.2 := rfl

/- ## Part 2: STEP 0 for multisets (ports of ML.Step0) -/

/-- If f vanishes for all j ≤ b then summing over 0..τ is the same as over b+1..τ. -/
lemma sum_range_eq_sum_Icc_of_lt_M {f : ℕ → ℝ} {b τ : ℕ} (hf : ∀ j ≤ b, f j = 0) :
    (∑ j ∈ Finset.range (τ + 1), f j) = (∑ j ∈ Finset.Icc (b + 1) τ, f j) := by
  classical
  calc
    (∑ j ∈ Finset.range (τ + 1), f j)
        = (∑ j ∈ Finset.range (τ + 1), (if b < j then f j else 0)) := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases h : b < j
          · simp [h]
          · have hjb : j ≤ b := by omega
            simp [h, hf j hjb]
    _ = (∑ j ∈ (Finset.range (τ + 1)).filter (fun j => b < j), f j) := by
          rw [Finset.sum_filter]
    _ = (∑ j ∈ Finset.Icc (b + 1) τ, f j) := by
          have hset : (Finset.range (τ + 1)).filter (fun j => b < j) = Finset.Icc (b + 1) τ := by
            ext j
            simp
            omega
          rw [hset]

/-- sCount is the size of the level-j piece -/
lemma sCount_eq_sizeM_levM (N0 : MSys X) (S' : X → ℕ) (j : ℕ) :
    N0.sCount S' j = sizeM (N0.levM S' j) := by
  classical
  unfold sCount sizeM levM
  rfl

/-- sCount = 0 forces the level piece to vanish -/
lemma levM_eq_zero_of_sCount_zero (N0 : MSys X) (S' : X → ℕ) (j : ℕ)
    (h : N0.sCount S' j = 0) : N0.levM S' j = 0 := by
  classical
  funext x
  have hsz : sizeM (N0.levM S' j) = 0 := by rw [← sCount_eq_sizeM_levM N0 S' j]; exact h
  have hxle : N0.levM S' j x ≤ sizeM (N0.levM S' j) :=
    Finset.single_le_sum (by intro y hy; exact Nat.zero_le _) (Finset.mem_univ x)
  have : N0.levM S' j x ≤ 0 := by simpa [hsz] using hxle
  exact le_antisymm this (Nat.zero_le _)

/-- prefixCount = 0 forces every level count ≤ b to vanish -/
lemma sCount_eq_zero_of_prefixM (N0 : MSys X) (S : X → ℕ) (b : ℕ)
    (hpre : N0.prefixCount S b = 0) : ∀ j, j ≤ b → N0.sCount S j = 0 := by
  intro j hj
  have hsum : (∑ j ∈ Finset.range (b + 1), N0.sCount S j) = 0 := by
    simpa [prefixCount] using hpre
  have hall : ∀ j ∈ Finset.range (b + 1), N0.sCount S j = 0 :=
    Finset.sum_eq_zero_iff.mp hsum
  exact hall j (by simpa using hj)

/-- weightAbove at a level with empty level piece is ≤ total weightM -/
lemma weightAboveM_le_weightM (N0 : MSys X) (S' A : X → ℕ) (b : ℕ) :
    N0.weightAboveM S' A b ≤ N0.weightM S' A := by
  classical
  unfold weightAboveM weightM
  refine Finset.sum_le_sum_of_subset_of_nonneg (s := Finset.Icc (b + 1) N0.τ)
    (t := Finset.range (N0.τ + 1)) ?_ ?_
  · intro j hj
    have hjb : b + 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjτ : j ≤ N0.τ := (Finset.mem_Icc.mp hj).2
    exact Finset.mem_range.mpr (by omega)
  · intro j hj hnot
    exact mul_nonneg (by exact_mod_cast (Nat.zero_le (N0.countAt S' A j))) (wlev_nonneg j)

/-- countAt of A at an empty level is zero -/
lemma countAt_eq_zero_of_sCount_zero (N0 : MSys X) (S' A : X → ℕ) (j : ℕ)
    (h : N0.sCount S' j = 0) : N0.countAt S' A j = 0 := by
  have hle : N0.countAt S' A j ≤ N0.sCount S' j := N0.countAt_le_sCount S' A j
  omega

/-- weightM = weightAboveM when levels ≤ b of S' are empty -/
lemma weightM_eq_weightAboveM_of_sCount_zero (N0 : MSys X) (S' A : X → ℕ) (b : ℕ)
    (h : ∀ j, j ≤ b → N0.sCount S' j = 0) :
    N0.weightM S' A = N0.weightAboveM S' A b := by
  classical
  calc
    N0.weightM S' A = (∑ j ∈ Finset.range (N0.τ + 1), (N0.countAt S' A j : ℝ) * wlev j) := rfl
    _ = (∑ j ∈ Finset.Icc (b + 1) N0.τ, (N0.countAt S' A j : ℝ) * wlev j) :=
          sum_range_eq_sum_Icc_of_lt_M (b := b) (τ := N0.τ)
            (f := fun j => (N0.countAt S' A j : ℝ) * wlev j)
            (by intro j hj
                have hc : N0.countAt S' A j = 0 := countAt_eq_zero_of_sCount_zero N0 S' A j (h j hj)
                simp [hc])
    _ = N0.weightAboveM S' A b := rfl

/-- MinIndex ≤ τ -/
lemma minIndexM_le_tau (N0 : MSys X) (S W : X → ℕ) (hS : S ∈ N0.F) (hB : N0.LevelBounded) :
    N0.MinIndexM S W hS hB ≤ N0.τ := by
  exact N0.minIndexM_min S W hS hB (subMM S W) S (N0.sdiff_isFragmentM S W hS hB)

/-- t ≥ 1 for a minimum fragment of a bad pair -/
lemma t_posM (N0 : MSys X) (S W U : X → ℕ) (b : ℕ) (hS : S ∈ N0.F) (hB : N0.LevelBounded)
    (hTot : ∀ T ∈ N0.F, ((10 : ℝ) ^ 8)⁻¹ ≤ N0.totalWeightM T)
    (hbad : N0.BadM ((10 : ℝ) ^ 10)⁻¹ W) (hmin : N0.MinFragmentAtM S W U b hS hB)
    {S' : X → ℕ} (hfr : N0.IsFragmentM S W U b S') : 1 ≤ sizeM U := by
  classical
  by_contra hnot
  have ht0 : sizeM U = 0 := by omega
  have hU0 : U = fun _ => 0 := by
    funext x
    by_contra hx
    have hxpos : 0 < U x := Nat.pos_of_ne_zero hx
    have hpos : 0 < sizeM U := (sizeM_pos_iff (m := U)).2 ⟨x, hxpos⟩
    omega
  have hprof : ∀ j ≤ b, N0.sCount S j = N0.sCount S' j := hfr.1.2
  have hS'F : S' ∈ N0.F := hfr.1.1
  have hb0 : (9 / 10 : ℝ) * (N0.prefixCount S b : ℝ) ≤ 0 := by
    have hb1 := nb_le_tM N0 S W U b hS hB hTot hbad hmin hfr
    simpa [ht0] using hb1
  have hpre0 : N0.prefixCount S b = 0 := by
    have hx0 : 0 ≤ (N0.prefixCount S b : ℝ) := by positivity
    have hx : (N0.prefixCount S b : ℝ) ≤ 0 := by nlinarith
    exact_mod_cast (le_antisymm hx hx0)
  have hpreS : ∀ j, j ≤ b → N0.sCount S j = 0 := sCount_eq_zero_of_prefixM N0 S b hpre0
  have hpreS' : ∀ j, j ≤ b → N0.sCount S' j = 0 := by
    intro j hj
    rw [← hprof j hj]
    exact hpreS j hj
  have hwS' : N0.totalWeightM S' = N0.weightAboveM S' S' b := by
    unfold totalWeightM
    exact weightM_eq_weightAboveM_of_sCount_zero N0 S' S' b hpreS'
  have hfr2 := hfr.2.2.2
  have hpre0'' : ((N0.prefixCount S b : ℝ) - (sizeM U : ℝ)) = 0 := by simp [hpre0, ht0]
  have hwtot : ((10 : ℝ) ^ 8)⁻¹ ≤ N0.totalWeightM S' := hTot S' hS'F
  have hlowW : ((10 : ℝ) ^ 10)⁻¹ ≤ N0.weightAboveM S' (addM W U) b := by
    have hten : ((10 : ℝ) ^ 10)⁻¹ ≤ (100 : ℝ)⁻¹ * N0.totalWeightM S' := by
      have heq : ((10 : ℝ) ^ 10)⁻¹ = (100 : ℝ)⁻¹ * ((10 : ℝ) ^ 8)⁻¹ := by
        have hpow : (10 : ℝ) ^ 10 = (10 : ℝ) ^ 8 * 100 := by
          rw [show (10 : ℕ) = 8 + 2 by norm_num]
          rw [pow_add]
          norm_num
        rw [hpow]
        field_simp
      have hmul := mul_le_mul_of_nonneg_left hwtot (by norm_num : 0 ≤ (100 : ℝ)⁻¹)
      nlinarith
    have hmain : (100 : ℝ)⁻¹ * N0.totalWeightM S' ≤ N0.weightAboveM S' (addM W U) b := by
      calc
        (100 : ℝ)⁻¹ * N0.totalWeightM S' = (100 : ℝ)⁻¹ * N0.weightAboveM S' S' b := by rw [hwS']
        _ = (100 : ℝ)⁻¹ * (N0.weightAboveM S' S' b - wlev b * ((N0.prefixCount S b : ℝ) - (sizeM U : ℝ))) := by
              rw [hpre0'']
              ring
        _ ≤ N0.weightAboveM S' (addM W U) b := hfr2
    exact le_trans hten hmain
  have hWU : addM W U = W := by
    funext x
    unfold addM
    rw [hU0]
    simp
  have hlowW' : ((10 : ℝ) ^ 10)⁻¹ ≤ N0.weightAboveM S' W b := by
    simpa [hWU] using hlowW
  have hleW : N0.weightAboveM S' W b ≤ N0.weightM S' W := weightAboveM_le_weightM N0 S' W b
  have hleProc : N0.weightM S' W ≤ N0.procValM W := by
    unfold procValM
    exact N0.le_mSup (v := fun T : X → ℕ => N0.weightM T W) hS'F
  have hbad' : N0.procValM W < ((10 : ℝ) ^ 10)⁻¹ := hbad
  nlinarith

/-- removing the top level from a sum over Icc when its term vanishes -/
lemma sum_Icc_succ_of_zero_M {a τ : ℕ} {f : ℕ → ℝ} (ha : a ≤ τ) (hf : f a = 0) :
    (∑ j ∈ Finset.Icc a τ, f j) = (∑ j ∈ Finset.Icc (a + 1) τ, f j) := by
  classical
  calc
    (∑ j ∈ Finset.Icc a τ, f j)
        = (∑ j ∈ Finset.Icc a τ, if a < j then f j else 0) := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases h : a < j
          · simp [h]
          · have hja : j = a := by
              have hj1 : a ≤ j := (Finset.mem_Icc.mp hj).1
              omega
            simp [h, hja, hf]
    _ = (∑ j ∈ (Finset.Icc a τ).filter (fun j => a < j), f j) := by rw [Finset.sum_filter]
    _ = (∑ j ∈ Finset.Icc (a + 1) τ, f j) := by
          have hset : (Finset.Icc a τ).filter (fun j => a < j) = Finset.Icc (a + 1) τ := by
            ext j
            simp
            omega
          rw [hset]

/-- weightAbove at level b-1 equals weightAbove at level b when the level-b piece of S' is empty -/
lemma weightAboveM_pred_eq (N0 : MSys X) (S' A : X → ℕ) (b : ℕ)
    (hlev : N0.levM S' b = 0) :
    N0.weightAboveM S' A (b - 1) = N0.weightAboveM S' A b := by
  classical
  by_cases hb0 : b = 0
  · subst b
    simp
  · have hb1 : 1 ≤ b := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hb0)
    have hbb : b - 1 + 1 = b := by omega
    by_cases hbτ : b ≤ N0.τ
    · unfold weightAboveM
      have hsplit := ObsTPrime.sum_Icc_split_at (a := b) (b := b) (c := N0.τ) (by omega) hbτ
        (fun j => (N0.countAt S' A j : ℝ) * wlev j)
      have htop : (∑ j ∈ Finset.Icc b b, (N0.countAt S' A j : ℝ) * wlev j) = 0 := by
        have hs : N0.sCount S' b = 0 := by
          rw [sCount_eq_sizeM_levM]
          rw [hlev]
          simp [sizeM]
        have hc : N0.countAt S' A b = 0 := countAt_eq_zero_of_sCount_zero N0 S' A b hs
        simp [hc]
      calc
        (∑ j ∈ Finset.Icc (b - 1 + 1) N0.τ, (N0.countAt S' A j : ℝ) * wlev j)
            = (∑ j ∈ Finset.Icc b N0.τ, (N0.countAt S' A j : ℝ) * wlev j) := by rw [hbb]
        _ = (∑ j ∈ Finset.Icc b b, (N0.countAt S' A j : ℝ) * wlev j)
            + (∑ j ∈ Finset.Icc (b + 1) N0.τ, (N0.countAt S' A j : ℝ) * wlev j) := by
              rw [← hsplit]
        _ = (∑ j ∈ Finset.Icc (b + 1) N0.τ, (N0.countAt S' A j : ℝ) * wlev j) := by rw [htop]; simp
    · have hge : N0.τ ≤ b - 1 := by omega
      have hge' : N0.τ ≤ b := by omega
      rw [N0.weightAboveM_eq_zero_of_b_ge S' A (b - 1) hge]
      rw [N0.weightAboveM_eq_zero_of_b_ge S' A b hge']

/-- prefixCount at b-1 equals prefixCount at b when s_b = 0 -/
lemma prefixCount_pred_eq_M (N0 : MSys X) (S : X → ℕ) (b : ℕ) (hb1 : 1 ≤ b)
    (hsb0 : N0.sCount S b = 0) : N0.prefixCount S (b - 1) = N0.prefixCount S b := by
  classical
  have hbb : b - 1 + 1 = b := by omega
  unfold prefixCount
  calc
    (∑ j ∈ Finset.range (b - 1 + 1), N0.sCount S j) = ∑ j ∈ Finset.range b, N0.sCount S j := by rw [hbb]
    _ = ∑ j ∈ Finset.range (b + 1), N0.sCount S j := by
          rw [Finset.sum_range_succ, hsb0]
          simp

/-- s_b ≠ 0 for a minimum fragment of a bad pair -/
lemma sb_ne_zeroM (N0 : MSys X) (S W U : X → ℕ) (b : ℕ) (hS : S ∈ N0.F) (hB : N0.LevelBounded)
    (hTot : ∀ T ∈ N0.F, ((10 : ℝ) ^ 8)⁻¹ ≤ N0.totalWeightM T)
    (hbad : N0.BadM ((10 : ℝ) ^ 10)⁻¹ W) (hmin : N0.MinFragmentAtM S W U b hS hB) :
    N0.sCount S b ≠ 0 := by
  classical
  intro hsb0
  rcases hmin.2.1 with ⟨S', hfr⟩
  by_cases hb0 : b = 0
  · subst b
    have hnb0 : N0.prefixCount S 0 = 0 := by
      unfold prefixCount
      simp [hsb0]
    have ht1 : (1 : ℝ) ≤ (sizeM U : ℝ) := by
      exact_mod_cast (t_posM N0 S W U 0 hS hB hTot hbad hmin hfr)
    have htn : (sizeM U : ℝ) ≤ (N0.prefixCount S 0 : ℝ) := by
      have hle := t_le_nbM N0 S W U 0 hS hB hmin hfr
      exact_mod_cast hle
    have hpre0 : (N0.prefixCount S 0 : ℝ) = 0 := by exact_mod_cast hnb0
    nlinarith
  · have hb1 : 1 ≤ b := by omega
    have hbtau : b ≤ N0.τ := by
      have hmi := N0.minIndexM_min S W hS hB (subMM S W) S (N0.sdiff_isFragmentM S W hS hB)
      rwa [← hmin.1] at hmi
    have hprof : ∀ j ≤ b, N0.sCount S j = N0.sCount S' j := hfr.1.2
    have hS'F : S' ∈ N0.F := hfr.1.1
    have hsb' : N0.sCount S' b = 0 := by
      have hp := hprof b (by omega)
      exact hp.symm.trans hsb0
    have hlev : N0.levM S' b = 0 := levM_eq_zero_of_sCount_zero N0 S' b hsb'
    let c : ℕ := b - 1
    have hcle : c ≤ b := by omega
    have hprof_c : ∀ j, j ≤ c → N0.sCount S j = N0.sCount S' j := by
      intro j hj
      exact hprof j (le_trans hj hcle)
    have hfr_c : N0.IsFragmentM S W U c S' := by
      constructor
      · constructor
        · exact hS'F
        · intro j hj
          exact hprof_c j hj
      · constructor
        · exact hfr.2.1
        · constructor
          · intro j hj
            exact hfr.2.2.1 j (le_trans hj hcle)
          · have hwA : N0.weightAboveM S' (addM W U) c = N0.weightAboveM S' (addM W U) b := by
              dsimp [c]
              exact weightAboveM_pred_eq N0 S' (addM W U) b hlev
            have hwS : N0.weightAboveM S' S' c = N0.weightAboveM S' S' b := by
              dsimp [c]
              exact weightAboveM_pred_eq N0 S' S' b hlev
            have hpc : N0.prefixCount S c = N0.prefixCount S b := by
              dsimp [c]
              exact prefixCount_pred_eq_M N0 S b hb1 hsb0
            have htn : (sizeM U : ℝ) ≤ (N0.prefixCount S b : ℝ) := by
              have hle := t_le_nbM N0 S W U b hS hB hmin hfr
              exact_mod_cast hle
            have hD : 0 ≤ ((N0.prefixCount S b : ℝ) - (sizeM U : ℝ)) := by nlinarith
            have hwlev : wlev b ≤ wlev c := wlev_le_of_le (by dsimp [c]; omega)
            have hRle : (100 : ℝ)⁻¹ * (N0.weightAboveM S' S' c - wlev c * ((N0.prefixCount S c : ℝ) - (sizeM U : ℝ))) ≤
                (100 : ℝ)⁻¹ * (N0.weightAboveM S' S' b - wlev b * ((N0.prefixCount S b : ℝ) - (sizeM U : ℝ))) := by
              rw [hwS, hpc]
              have hm : wlev b * ((N0.prefixCount S b : ℝ) - (sizeM U : ℝ)) ≤
                  wlev c * ((N0.prefixCount S b : ℝ) - (sizeM U : ℝ)) :=
                mul_le_mul_of_nonneg_right hwlev hD
              nlinarith
            calc
              N0.weightAboveM S' (addM W U) c
                  = N0.weightAboveM S' (addM W U) b := hwA
              _ ≥ (100 : ℝ)⁻¹ * (N0.weightAboveM S' S' b - wlev b * ((N0.prefixCount S b : ℝ) - (sizeM U : ℝ))) := hfr.2.2.2
              _ ≥ (100 : ℝ)⁻¹ * (N0.weightAboveM S' S' c - wlev c * ((N0.prefixCount S c : ℝ) - (sizeM U : ℝ))) := hRle
    have hU' : N0.HasFragmentAtM S W U c := ⟨S', hfr_c⟩
    have hminle : N0.MinIndexM S W hS hB ≤ c := N0.minIndexM_min S W hS hB U S' hfr_c
    have hminb : b = N0.MinIndexM S W hS hB := hmin.1
    have : b ≤ c := by rw [hminb]; exact hminle
    omega

/- ## Pair facts -/

section PairFacts

variable (N0 : MSys X) (M : ℕ) (hB : N0.LevelBounded)

/-- MinFragmentAt for the pair. -/
lemma pair_minFragmentAt {x : (X → ℕ) × (X → ℕ)} (hx : x ∈ pairSet N0 M hB) :
    N0.MinFragmentAtM (witness N0 hB x.1 x.2) x.1 x.2 (bOf N0 hB x)
      (witness_mem N0 hB x.1 x.2 (pairSet_mem_cover hx)) hB := by
  classical
  have hs := pair_minFrag hx
  have hmi := N0.minFragM_spec (witness N0 hB x.1 x.2) x.1
    (witness_mem N0 hB x.1 x.2 (pairSet_mem_cover hx)) hB
  unfold bOf
  rw [dif_pos (pairSet_mem_cover hx)]
  simpa [hs] using hmi

/-- witness of the pair's minimum fragment -/
lemma pair_hasFragment {x : (X → ℕ) × (X → ℕ)} (hx : x ∈ pairSet N0 M hB) :
    ∃ S' : X → ℕ, N0.IsFragmentM (witness N0 hB x.1 x.2) x.1 x.2 (bOf N0 hB x) S' := by
  have hmi := pair_minFragmentAt N0 M hB hx
  exact hmi.2.1

/-- t ≤ n_b for a pair -/
lemma pair_t_le_nb {x : (X → ℕ) × (X → ℕ)} (hx : x ∈ pairSet N0 M hB) :
    (sizeM x.2 : ℝ) ≤ (N0.prefixCount (witness N0 hB x.1 x.2) (bOf N0 hB x) : ℝ) := by
  rcases pair_hasFragment N0 M hB hx with ⟨S', hfr⟩
  have hmi := pair_minFragmentAt N0 M hB hx
  have hle := t_le_nbM N0 (witness N0 hB x.1 x.2) x.1 x.2 (bOf N0 hB x)
    (witness_mem N0 hB x.1 x.2 (pairSet_mem_cover hx)) hB hmi hfr
  exact_mod_cast hle

/-- (9/10)·n_b ≤ t for a pair (bad) -/
lemma pair_nb_le_t {x : (X → ℕ) × (X → ℕ)} (hx : x ∈ pairSet N0 M hB)
    (hTot : ∀ T ∈ N0.F, ((10 : ℝ) ^ 8)⁻¹ ≤ N0.totalWeightM T) :
    (9 / 10 : ℝ) * (N0.prefixCount (witness N0 hB x.1 x.2) (bOf N0 hB x) : ℝ) ≤ (sizeM x.2 : ℝ) := by
  rcases pair_hasFragment N0 M hB hx with ⟨S', hfr⟩
  have hmi := pair_minFragmentAt N0 M hB hx
  have hbad := pair_bad hx
  exact nb_le_tM N0 (witness N0 hB x.1 x.2) x.1 x.2 (bOf N0 hB x)
    (witness_mem N0 hB x.1 x.2 (pairSet_mem_cover hx)) hB hTot hbad hmi hfr

/-- t ≥ 1 -/
lemma pair_t_pos {x : (X → ℕ) × (X → ℕ)} (hx : x ∈ pairSet N0 M hB)
    (hTot : ∀ T ∈ N0.F, ((10 : ℝ) ^ 8)⁻¹ ≤ N0.totalWeightM T) : 1 ≤ sizeM x.2 := by
  rcases pair_hasFragment N0 M hB hx with ⟨S', hfr⟩
  have hmi := pair_minFragmentAt N0 M hB hx
  have hbad := pair_bad hx
  exact t_posM N0 (witness N0 hB x.1 x.2) x.1 x.2 (bOf N0 hB x)
    (witness_mem N0 hB x.1 x.2 (pairSet_mem_cover hx)) hB hTot hbad hmi hfr

/-- the profile (counts) of the pair's witness at its own top level is nonzero -/
lemma pair_sb_ne_zero {x : (X → ℕ) × (X → ℕ)} (hx : x ∈ pairSet N0 M hB)
    (hTot : ∀ T ∈ N0.F, ((10 : ℝ) ^ 8)⁻¹ ≤ N0.totalWeightM T) :
    N0.sCount (witness N0 hB x.1 x.2) (bOf N0 hB x) ≠ 0 := by
  have hmi := pair_minFragmentAt N0 M hB hx
  have hbad := pair_bad hx
  exact sb_ne_zeroM N0 (witness N0 hB x.1 x.2) x.1 x.2 (bOf N0 hB x)
    (witness_mem N0 hB x.1 x.2 (pairSet_mem_cover hx)) hB hTot hbad hmi

/-- n_b ≥ 1 for a pair -/
lemma pair_nb_pos {x : (X → ℕ) × (X → ℕ)} (hx : x ∈ pairSet N0 M hB)
    (hTot : ∀ T ∈ N0.F, ((10 : ℝ) ^ 8)⁻¹ ≤ N0.totalWeightM T) :
    1 ≤ N0.prefixCount (witness N0 hB x.1 x.2) (bOf N0 hB x) := by
  have htn := pair_t_le_nb N0 M hB hx
  have ht1 : (1 : ℝ) ≤ (sizeM x.2 : ℝ) := by exact_mod_cast pair_t_pos N0 M hB hx hTot
  have : (1 : ℝ) ≤ (N0.prefixCount (witness N0 hB x.1 x.2) (bOf N0 hB x) : ℝ) := le_trans ht1 htn
  exact_mod_cast this

/-- b ≤ τ for a pair -/
lemma pair_b_le_tau {x : (X → ℕ) × (X → ℕ)} (hx : x ∈ pairSet N0 M hB) :
    bOf N0 hB x ≤ N0.τ := by
  classical
  unfold bOf
  rw [dif_pos (pairSet_mem_cover hx)]
  exact minIndexM_le_tau N0 (witness N0 hB x.1 x.2) x.1
    (witness_mem N0 hB x.1 x.2 (pairSet_mem_cover hx)) hB

/-- profile values of a pair's witness are legal at levels ≤ τ (from FLegalM) -/
lemma pair_legal (hLeg : N0.FLegalM) {x : (X → ℕ) × (X → ℕ)} (hx : x ∈ pairSet N0 M hB)
    {j : ℕ} (hj : j ≤ N0.τ) :
    Sel.Deep.Sys.LegalEntry (N0.sCount (witness N0 hB x.1 x.2) j) j := by
  unfold FLegalM at hLeg
  exact hLeg (witness N0 hB x.1 x.2) (witness_mem N0 hB x.1 x.2 (pairSet_mem_cover hx)) j hj

/-- the pair's U is contained in its witness S∖W -/
lemma pair_subM_sdiff {x : (X → ℕ) × (X → ℕ)} (hx : x ∈ pairSet N0 M hB) :
    subM x.2 (subMM (witness N0 hB x.1 x.2) x.1) := by
  have hs := pair_minFrag hx
  have hsub := N0.minFragM_subM_sdiff (witness N0 hB x.1 x.2) x.1
    (witness_mem N0 hB x.1 x.2 (pairSet_mem_cover hx)) hB
  simpa [hs] using hsub

/-- witness of a pair -/
noncomputable def pw (N0 : MSys X) (hB : N0.LevelBounded) (x : (X → ℕ) × (X → ℕ)) : X → ℕ :=
  witness N0 hB x.1 x.2

lemma pw_mem {x : (X → ℕ) × (X → ℕ)} (hx : x ∈ pairSet N0 M hB) : pw N0 hB x ∈ N0.F :=
  witness_mem N0 hB x.1 x.2 (pairSet_mem_cover hx)

/-- group keys equal implies the levels agree -/
lemma groupKey_b_eq (x : (X → ℕ) × (X → ℕ)) (k : ℕ × (ℕ → ℕ)) (hx : x ∈ pairSet N0 M hB)
    (hk : groupKey N0 hB x = k) : bOf N0 hB x = k.1 := by
  simpa [groupKey] using (congrArg Prod.fst hk)

/-- any pair with key (b,s) has sCount of its witness equal to the key profile on j ≤ b -/
lemma groupKey_profile (x : (X → ℕ) × (X → ℕ)) (k : ℕ × (ℕ → ℕ)) (hx : x ∈ pairSet N0 M hB)
    (hk : groupKey N0 hB x = k) : ∀ j, j ≤ k.1 → N0.sCount (pw N0 hB x) j = k.2 j := by
  intro j hj
  have hb : bOf N0 hB x = k.1 := groupKey_b_eq N0 M hB x k hx hk
  have hs : sOf N0 hB x j = k.2 j := by
    simpa [groupKey] using (congrArg (fun q : ℕ × (ℕ → ℕ) => q.2 j) hk)
  have hb2 : j ≤ bOf N0 hB x := by
    rw [hb]
    exact hj
  have hif : N0.sCount (witness N0 hB x.1 x.2) j = k.2 j := by
    have : (if j ≤ bOf N0 hB x then N0.sCount (witness N0 hB x.1 x.2) j else 0) = k.2 j := by
      simpa [sOf] using hs
    rwa [if_pos hb2] at this
  simpa [pw] using hif

/-- keyTotal equals the prefix count of the pair's witness at its own level -/
lemma keyTotal_eq_prefix (x : (X → ℕ) × (X → ℕ)) (k : ℕ × (ℕ → ℕ)) (hx : x ∈ pairSet N0 M hB)
    (hk : groupKey N0 hB x = k) : keyTotal k = N0.prefixCount (pw N0 hB x) (bOf N0 hB x) := by
  have hb : bOf N0 hB x = k.1 := groupKey_b_eq N0 M hB x k hx hk
  unfold keyTotal
  unfold prefixCount
  rw [hb]
  apply Finset.sum_congr rfl
  intro j hj
  have hjb : j ≤ k.1 := by simpa using hj
  exact (groupKey_profile N0 M hB x k hx hk j hjb).symm

/-- every pair in the fiber has its t in fiberTs k -/
lemma fiber_mem_Ts {k : ℕ × (ℕ → ℕ)} {x : (X → ℕ) × (X → ℕ)} (hx : x ∈ fiber N0 M hB k)
    (hTot : ∀ T ∈ N0.F, ((10 : ℝ) ^ 8)⁻¹ ≤ N0.totalWeightM T) : sizeM x.2 ∈ fiberTs k := by
  classical
  have hx1 : x ∈ pairSet N0 M hB ∧ groupKey N0 hB x = k := by
    simpa [fiber] using hx
  have hxpair : x ∈ pairSet N0 M hB := hx1.1
  have hxkey : groupKey N0 hB x = k := hx1.2
  have hnb : keyTotal k = N0.prefixCount (pw N0 hB x) (bOf N0 hB x) :=
    keyTotal_eq_prefix N0 M hB x k hxpair hxkey
  have htl : (sizeM x.2 : ℝ) ≤ (N0.prefixCount (pw N0 hB x) (bOf N0 hB x) : ℝ) :=
    pair_t_le_nb N0 M hB hxpair
  have htge : (9 / 10 : ℝ) * (N0.prefixCount (pw N0 hB x) (bOf N0 hB x) : ℝ) ≤ (sizeM x.2 : ℝ) :=
    pair_nb_le_t N0 M hB hxpair hTot
  unfold fiberTs
  have htln : sizeM x.2 ≤ keyTotal k := by
    rw [hnb]
    exact_mod_cast htl
  have htgn : (9 / 10 : ℝ) * (keyTotal k : ℝ) ≤ (sizeM x.2 : ℝ) := by
    rwa [← hnb] at htge
  exact Finset.mem_filter.mpr ⟨by simpa using htln, htgn⟩

end PairFacts

/- ## Part 3: fragment witnesses, common prefixes, sub-multiset counting -/

/-- the fragment witness S' of a pair (junk outside pairSet) -/
noncomputable def fragWitnessOf (N0 : MSys X) (M : ℕ) (hB : N0.LevelBounded)
    (x : (X → ℕ) × (X → ℕ)) : X → ℕ := by
  classical
  exact if hx : x ∈ pairSet N0 M hB then
    Classical.choose (pair_hasFragment N0 M hB hx) else fun _ => 0

lemma fragWitness_mem {N0 : MSys X} {M : ℕ} {hB : N0.LevelBounded} {x : (X → ℕ) × (X → ℕ)}
    (hx : x ∈ pairSet N0 M hB) : fragWitnessOf N0 M hB x ∈ N0.F := by
  classical
  unfold fragWitnessOf
  rw [dif_pos hx]
  have hfr := Classical.choose_spec (pair_hasFragment N0 M hB hx)
  exact hfr.1.1

lemma fragWitness_profile {N0 : MSys X} {M : ℕ} {hB : N0.LevelBounded} {x : (X → ℕ) × (X → ℕ)}
    (hx : x ∈ pairSet N0 M hB) :
    ∀ j, j ≤ bOf N0 hB x → N0.sCount (fragWitnessOf N0 M hB x) j = N0.sCount (pw N0 hB x) j := by
  classical
  intro j hj
  unfold fragWitnessOf
  rw [dif_pos hx]
  have hfr := Classical.choose_spec (pair_hasFragment N0 M hB hx)
  exact (hfr.1.2 j hj).symm

lemma fragWitness_frag1 {N0 : MSys X} {M : ℕ} {hB : N0.LevelBounded} {x : (X → ℕ) × (X → ℕ)}
    (hx : x ∈ pairSet N0 M hB) :
    ∀ j, j ≤ bOf N0 hB x → subM (N0.levM (fragWitnessOf N0 M hB x) j) (addM x.1 x.2) := by
  classical
  intro j hj
  unfold fragWitnessOf
  rw [dif_pos hx]
  have hfr := Classical.choose_spec (pair_hasFragment N0 M hB hx)
  exact hfr.2.2.1 j hj

lemma fragWitness_frag2 {N0 : MSys X} {M : ℕ} {hB : N0.LevelBounded} {x : (X → ℕ) × (X → ℕ)}
    (hx : x ∈ pairSet N0 M hB) :
    N0.weightAboveM (fragWitnessOf N0 M hB x) (addM x.1 x.2) (bOf N0 hB x) ≥ (100 : ℝ)⁻¹ *
      (N0.weightAboveM (fragWitnessOf N0 M hB x) (fragWitnessOf N0 M hB x) (bOf N0 hB x) -
        wlev (bOf N0 hB x) *
          ((N0.prefixCount (pw N0 hB x) (bOf N0 hB x) : ℝ) - (sizeM x.2 : ℝ))) := by
  classical
  unfold fragWitnessOf
  rw [dif_pos hx]
  have hfr := Classical.choose_spec (pair_hasFragment N0 M hB hx)
  simpa [pw] using hfr.2.2.2

/-- the U of a pair lies in the prefix of the fragment witness of ANY pair with the same key
    and the same Z -/
lemma U_subM_prefixM_of_common (N0 : MSys X) (M : ℕ) (hB : N0.LevelBounded)
    (x y : (X → ℕ) × (X → ℕ)) (hx : x ∈ pairSet N0 M hB) (hy : y ∈ pairSet N0 M hB)
    (hkx : groupKey N0 hB x = groupKey N0 hB y)
    (hZ : addM x.1 x.2 = addM y.1 y.2) (ht : sizeM x.2 = sizeM y.2) :
    subM x.2 (N0.prefixM (fragWitnessOf N0 M hB y) (bOf N0 hB y)) := by
  classical
  let k : ℕ × (ℕ → ℕ) := groupKey N0 hB y
  have hky : groupKey N0 hB y = k := rfl
  have hkx' : groupKey N0 hB x = k := by simpa [k] using hkx
  have hbxy : bOf N0 hB x = bOf N0 hB y := by
    have h1 := groupKey_b_eq N0 M hB y k hy hky
    have h2 := groupKey_b_eq N0 M hB x k hx hkx'
    rw [h1, h2]
  let Sh : X → ℕ := fragWitnessOf N0 M hB y
  let Sx : X → ℕ := pw N0 hB x
  let Sy : X → ℕ := pw N0 hB y
  have hSyF : Sy ∈ N0.F := pw_mem N0 M hB hy
  have hSxF : Sx ∈ N0.F := pw_mem N0 M hB hx
  have hShF : Sh ∈ N0.F := fragWitness_mem hy
  have hminx0 : N0.MinFragmentAtM Sx x.1 x.2 (bOf N0 hB x) hSxF hB := by
    dsimp [Sx]
    exact pair_minFragmentAt N0 M hB hx
  have hminx : N0.MinFragmentAtM Sx x.1 x.2 (bOf N0 hB y) hSxF hB := by
    simpa [hbxy] using hminx0
  have hprof : ∀ j, j ≤ bOf N0 hB y → N0.sCount Sh j = N0.sCount Sx j := by
    intro j hj
    have h1 : N0.sCount Sh j = N0.sCount Sy j := by
      dsimp [Sh]
      exact fragWitness_profile hy j hj
    have h2 : N0.sCount Sy j = N0.sCount Sx j := by
      have hb' : bOf N0 hB y = k.1 := groupKey_b_eq N0 M hB y k hy hky
      have hj' : j ≤ k.1 := by
        rw [← hb']
        exact hj
      have a1 := groupKey_profile N0 M hB x k hx hkx' j hj'
      have a2 := groupKey_profile N0 M hB y k hy hky j hj'
      unfold Sy Sx
      exact a2.trans a1.symm
    exact h1.trans h2
  have hfeas1 : ∀ j, j ≤ bOf N0 hB y → subM (N0.levM Sh j) (addM x.1 x.2) := by
    intro j hj
    have hf := fragWitness_frag1 hy j hj
    rw [← hZ] at hf
    simpa [Sh] using hf
  have hfeas2 : N0.weightAboveM Sh (addM x.1 x.2) (bOf N0 hB y) ≥ (100 : ℝ)⁻¹ *
      (N0.weightAboveM Sh Sh (bOf N0 hB y) - wlev (bOf N0 hB y) *
        ((N0.prefixCount Sx (bOf N0 hB y) : ℝ) - (sizeM x.2 : ℝ))) := by
    have hf := fragWitness_frag2 hy
    have hf' : N0.weightAboveM Sh (addM y.1 y.2) (bOf N0 hB y) ≥ (100 : ℝ)⁻¹ *
        (N0.weightAboveM Sh Sh (bOf N0 hB y) - wlev (bOf N0 hB y) *
          ((N0.prefixCount Sy (bOf N0 hB y) : ℝ) - (sizeM y.2 : ℝ))) := by
      simpa [Sh, Sy, pw] using hf
    have hpreN : N0.prefixCount Sy (bOf N0 hB y) = N0.prefixCount Sx (bOf N0 hB y) := by
      unfold prefixCount
      apply Finset.sum_congr rfl
      intro j hj
      have hjb : j ≤ bOf N0 hB y := by simpa using hj
      have hb' : bOf N0 hB y = k.1 := groupKey_b_eq N0 M hB y k hy hky
      have hj' : j ≤ k.1 := by
        rw [← hb']
        exact hjb
      have h1 := groupKey_profile N0 M hB x k hx hkx' j hj'
      have h2 := groupKey_profile N0 M hB y k hy hky j hj'
      unfold Sy Sx
      exact h2.trans h1.symm
    have hpreR : (N0.prefixCount Sy (bOf N0 hB y) : ℝ) = (N0.prefixCount Sx (bOf N0 hB y) : ℝ) := by
      exact_mod_cast hpreN
    have htR : (sizeM y.2 : ℝ) = (sizeM x.2 : ℝ) := by exact_mod_cast ht.symm
    rw [hpreR, htR] at hf'
    rw [← hZ] at hf'
    simpa [Sh] using hf'
  have hfrx : N0.IsFragmentM Sx x.1 x.2 (bOf N0 hB y) Sh := by
    constructor
    · constructor
      · exact hShF
      · intro j hj
        exact (hprof j hj).symm
    · constructor
      · simpa [Sx, pw] using pair_subM_sdiff N0 M hB hx
      · constructor
        · exact hfeas1
        · exact hfeas2
  have hmain := minFragM_subM_prefixM N0 Sx x.1 x.2 (bOf N0 hB y) hSxF hB hminx hfrx
  simpa [Sh, Sx] using hmain

/-- size of the prefix of a pair's fragment witness equals the key total -/
lemma prefix_sizeM_of_pair (N0 : MSys X) (M : ℕ) (hB : N0.LevelBounded)
    (x : (X → ℕ) × (X → ℕ)) (k : ℕ × (ℕ → ℕ)) (hx : x ∈ pairSet N0 M hB)
    (hk : groupKey N0 hB x = k) :
    sizeM (N0.prefixM (fragWitnessOf N0 M hB x) (bOf N0 hB x)) = keyTotal k := by
  classical
  have h1 : sizeM (N0.prefixM (fragWitnessOf N0 M hB x) (bOf N0 hB x)) =
      N0.prefixCount (fragWitnessOf N0 M hB x) (bOf N0 hB x) :=
    N0.sizeM_prefixM (fragWitnessOf N0 M hB x) (bOf N0 hB x)
  calc
    sizeM (N0.prefixM (fragWitnessOf N0 M hB x) (bOf N0 hB x))
        = N0.prefixCount (fragWitnessOf N0 M hB x) (bOf N0 hB x) := h1
    _ = N0.prefixCount (pw N0 hB x) (bOf N0 hB x) := by
          unfold prefixCount
          apply Finset.sum_congr rfl
          intro j hj
          exact fragWitness_profile hx j (by simpa using hj)
    _ = keyTotal k := (keyTotal_eq_prefix N0 M hB x k hx hk).symm

/-- sub-multisets of A form a finset -/
noncomputable def subMsets (A : X → ℕ) : Finset (X → ℕ) := by
  classical
  exact (Finset.univ : Finset (∀ y : X, Fin (A y + 1))).image (fun v => fun y => (v y).val)

lemma mem_subMsets {A m : X → ℕ} : m ∈ subMsets A ↔ subM m A := by
  classical
  unfold subMsets
  rw [Finset.mem_image]
  constructor
  · rintro ⟨v, hv, hvm⟩
    intro y
    have hvle : (v y).val < A y + 1 := (v y).isLt
    have hm : m y = (v y).val := (congrFun hvm y).symm
    omega
  · intro h
    let v : ∀ y : X, Fin (A y + 1) := fun y => ⟨m y, Nat.lt_succ_of_le (h y)⟩
    refine ⟨v, Finset.mem_univ v, ?_⟩
    funext y
    rfl

lemma card_subMsets (A : X → ℕ) : (subMsets A).card = ∏ y : X, (A y + 1) := by
  classical
  unfold subMsets
  have hinj : Set.InjOn (fun v : ∀ y : X, Fin (A y + 1) => fun y => (v y).val)
      ↑(Finset.univ : Finset (∀ y : X, Fin (A y + 1))) := by
    intro v hv w hw hvw
    funext y
    apply Fin.ext
    exact congrFun hvw y
  rw [Finset.card_image_of_injOn hinj]
  simp

/-- n.choose k ≤ 2^n -/
lemma choose_le_two_pow (n k : ℕ) : n.choose k ≤ 2 ^ n := by
  by_cases hk : k ≤ n
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hk0 : k = 0 := by omega
      subst k
      norm_num
    · exact (Nat.choose_lt_two_pow n k hn).le
  · have hz : n.choose k = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)
    rw [hz]
    exact Nat.zero_le _

lemma choose_le_two_pow_real (n k : ℕ) : ((n.choose k : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
  exact_mod_cast (choose_le_two_pow n k)

lemma add_one_le_two_pow_nat (m : ℕ) : m + 1 ≤ 2 ^ m := by
  classical
  induction m with
  | zero => norm_num
  | succ m ih =>
      have hstep : (m + 1) + 1 ≤ 2 * (m + 1) := by omega
      have hle2 : 2 * (m + 1) ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 ih
      calc
        (m + 1) + 1 ≤ 2 * (m + 1) := hstep
        _ ≤ 2 * 2 ^ m := hle2
        _ = 2 ^ (m + 1) := by
              rw [pow_succ]
              ring

lemma one_le_two_pow_nat (m : ℕ) : 1 ≤ 2 ^ m := by
  exact one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)

lemma card_subMsets_le (A : X → ℕ) : (subMsets A).card ≤ 2 ^ sizeM A := by
  classical
  calc
    (subMsets A).card = ∏ y : X, (A y + 1) := card_subMsets A
    _ ≤ ∏ y : X, 2 ^ A y := by
          exact Finset.prod_le_prod (by intro y hy; exact Nat.zero_le _)
            (by intro y hy; exact add_one_le_two_pow_nat (A y))
    _ = 2 ^ (∑ y : X, A y) := by rw [Finset.prod_pow_eq_pow_sum]
    _ = 2 ^ sizeM A := rfl

/-- binomial product of a pair is at most 2^{keyTotal} -/
lemma pair_binom_le (N0 : MSys X) (M : ℕ) (hB : N0.LevelBounded)
    {x : (X → ℕ) × (X → ℕ)} (hx : x ∈ pairSet N0 M hB) :
    (∏ y : X, (((addM x.1 x.2) y).choose (x.2 y) : ℝ)) ≤ (2 : ℝ) ^ keyTotal (groupKey N0 hB x) := by
  classical
  rcases pair_hasFragment N0 M hB hx with ⟨S', hfr⟩
  have hmi := pair_minFragmentAt N0 M hB hx
  have hSxF : pw N0 hB x ∈ N0.F := pw_mem N0 M hB hx
  let b : ℕ := bOf N0 hB x
  let A : X → ℕ := N0.prefixM S' b
  have hob : ∀ y, A y - x.1 y = x.2 y := by
    intro y
    have hT := obsTM N0 (pw N0 hB x) x.1 x.2 b hSxF hB hmi hfr
    dsimp [A]
    exact congrFun hT y
  have hsizeA : sizeM A = keyTotal (groupKey N0 hB x) := by
    dsimp [A]
    have h1 : sizeM (N0.prefixM S' b) = N0.prefixCount S' b := N0.sizeM_prefixM S' b
    calc
      sizeM (N0.prefixM S' b) = N0.prefixCount S' b := h1
      _ = N0.prefixCount (pw N0 hB x) b := by
            unfold prefixCount
            apply Finset.sum_congr rfl
            intro j hj
            exact (hfr.1.2 j (by simpa using hj)).symm
      _ = keyTotal (groupKey N0 hB x) := by
            have hk := keyTotal_eq_prefix N0 M hB x (groupKey N0 hB x) hx rfl
            change N0.prefixCount (pw N0 hB x) (bOf N0 hB x) = keyTotal (groupKey N0 hB x)
            exact hk.symm
  have hcoef : ∀ y, (((addM x.1 x.2) y).choose (x.2 y) : ℝ) ≤ (2 : ℝ) ^ A y := by
    intro y
    by_cases hU : x.2 y = 0
    · have hch : (((addM x.1 x.2) y).choose (x.2 y) : ℕ) = 1 := by
        rw [hU]
        simp [addM]
      rw [hch]
      have h1n : (1 : ℕ) ≤ 2 ^ A y := one_le_two_pow_nat (A y)
      exact_mod_cast h1n
    · have hU1 : 1 ≤ x.2 y := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hU)
      have hobs : A y - x.1 y = x.2 y := hob y
      have hA : x.1 y < A y := by omega
      have hZy : (addM x.1 x.2) y = A y := by
        unfold addM
        have hsub : x.1 y + (A y - x.1 y) = A y := Nat.add_sub_of_le (le_of_lt hA)
        rwa [hobs] at hsub
      have hch : (((addM x.1 x.2) y).choose (x.2 y) : ℝ) ≤ (2 : ℝ) ^ ((addM x.1 x.2) y) := by
        exact_mod_cast (choose_le_two_pow ((addM x.1 x.2) y) (x.2 y))
      rw [hZy] at hch ⊢
      exact hch
  calc
    (∏ y : X, (((addM x.1 x.2) y).choose (x.2 y) : ℝ))
        ≤ ∏ y : X, (2 : ℝ) ^ A y := by
            exact Finset.prod_le_prod (by intro y hy; exact_mod_cast (Nat.zero_le _))
              (by intro y hy; exact hcoef y)
    _ = (2 : ℝ) ^ sizeM A := by
            rw [Finset.prod_pow_eq_pow_sum]
            rfl
    _ = (2 : ℝ) ^ keyTotal (groupKey N0 hB x) := by rw [hsizeA]

/- ## Part 4: the Z-side bound -/

/-- generic: a sum over a finset equals the sum over the g-fibers -/
lemma sum_fiberwise_M {α β : Type*} {M0 : Type*} [AddCommMonoid M0] (s : Finset α)
    (g : α → β) (w : α → M0) :
    (∑ x ∈ s, w x) = ∑ k ∈ s.image g, ∑ x ∈ s.filter (fun x => g x = k), w x := by
  classical
  let T : Finset β := s.image g
  let F : β → Finset α := fun k => s.filter (fun x => g x = k)
  have hcover : s = T.biUnion F := by
    ext x
    constructor
    · intro hx
      exact Finset.mem_biUnion.mpr ⟨g x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
    · intro hx
      rcases (Finset.mem_biUnion.mp hx) with ⟨k, hkT, hxF⟩
      exact (Finset.mem_filter.mp hxF).1
  have hdisj : (T : Set β).Pairwise (fun k k' => Disjoint (F k) (F k')) := by
    intro k hk k' hk' hkk'
    rw [Finset.disjoint_left]
    intro x hx hx'
    apply hkk'
    have h1 : g x = k := (Finset.mem_filter.mp hx).2
    have h2 : g x = k' := (Finset.mem_filter.mp hx').2
    rw [← h1, ← h2]
  calc
    (∑ x ∈ s, w x) = ∑ x ∈ T.biUnion F, w x := by rw [hcover]
    _ = ∑ k ∈ T, ∑ x ∈ F k, w x := Finset.sum_biUnion hdisj
    _ = ∑ k ∈ s.image g, ∑ x ∈ s.filter (fun x => g x = k), w x := rfl

/-- inner sum over the preimage of one Z is at most 2^{2·keyTotal k} -/
lemma fiber_Z_inner_le (N0 : MSys X) (M : ℕ) (hB : N0.LevelBounded)
    (k : ℕ × (ℕ → ℕ)) (t : ℕ) (x0 : (X → ℕ) × (X → ℕ)) (hx0 : x0 ∈ fiberT N0 M hB k t) :
    (∑ x ∈ (fiberT N0 M hB k t).filter (fun x => addM x.1 x.2 = addM x0.1 x0.2),
        (∏ y : X, (((addM x.1 x.2) y).choose (x.2 y) : ℝ)))
      ≤ (2 : ℝ) ^ (2 * keyTotal k) := by
  classical
  let Z : X → ℕ := addM x0.1 x0.2
  let pre : Finset ((X → ℕ) × (X → ℕ)) :=
    (fiberT N0 M hB k t).filter (fun x => addM x.1 x.2 = Z)
  have hx0' : x0 ∈ pre := by
    dsimp [pre]
    exact Finset.mem_filter.mpr ⟨hx0, rfl⟩
  have hsub : ∀ x ∈ pre, subM x.2 (N0.prefixM (fragWitnessOf N0 M hB x0) (bOf N0 hB x0)) := by
    intro x hx
    have hxT : x ∈ fiberT N0 M hB k t := (Finset.mem_filter.mp hx).1
    have hxf : x ∈ fiber N0 M hB k := (Finset.mem_filter.mp hxT).1
    have hxpair : x ∈ pairSet N0 M hB := (Finset.mem_filter.mp hxf).1
    have hxkey : groupKey N0 hB x = k := (Finset.mem_filter.mp hxf).2
    have hxt : sizeM x.2 = t := (Finset.mem_filter.mp hxT).2
    have hx0T : x0 ∈ fiberT N0 M hB k t := hx0
    have hx0f : x0 ∈ fiber N0 M hB k := (Finset.mem_filter.mp hx0T).1
    have hx0pair : x0 ∈ pairSet N0 M hB := (Finset.mem_filter.mp hx0f).1
    have hx0key : groupKey N0 hB x0 = k := (Finset.mem_filter.mp hx0f).2
    have hx0t : sizeM x0.2 = t := (Finset.mem_filter.mp hx0T).2
    have hZx : addM x.1 x.2 = Z := (Finset.mem_filter.mp hx).2
    have hZx0 : addM x0.1 x0.2 = Z := rfl
    have hm := U_subM_prefixM_of_common N0 M hB x x0 hxpair hx0pair
      (by rw [hxkey, hx0key]) (by rw [hZx, hZx0]) (by rw [hxt, hx0t])
    simpa [Z] using hm
  let A0 : X → ℕ := N0.prefixM (fragWitnessOf N0 M hB x0) (bOf N0 hB x0)
  have hA0size : sizeM A0 = keyTotal k := by
    dsimp [A0]
    have hx0T : x0 ∈ fiberT N0 M hB k t := hx0
    have hx0f : x0 ∈ fiber N0 M hB k := (Finset.mem_filter.mp hx0T).1
    have hx0pair : x0 ∈ pairSet N0 M hB := (Finset.mem_filter.mp hx0f).1
    have hx0key : groupKey N0 hB x0 = k := (Finset.mem_filter.mp hx0f).2
    exact prefix_sizeM_of_pair N0 M hB x0 k hx0pair hx0key
  have hmap : ∀ x ∈ pre, x.2 ∈ subMsets A0 := by
    intro x hx
    exact (mem_subMsets).2 (hsub x hx)
  have hinj : Set.InjOn (fun x : (X → ℕ) × (X → ℕ) => x.2) (↑pre : Set ((X → ℕ) × (X → ℕ))) := by
    intro x hx y hy hxy
    have hZx : addM x.1 x.2 = Z := (Finset.mem_filter.mp hx).2
    have hZy : addM y.1 y.2 = Z := (Finset.mem_filter.mp hy).2
    have hx1 : x.1 = subMM Z x.2 := by
      funext u
      unfold subMM
      have hadd : x.1 u + x.2 u = Z u := congrFun hZx u
      omega
    have hy1 : y.1 = subMM Z y.2 := by
      funext u
      unfold subMM
      have hadd : y.1 u + y.2 u = Z u := congrFun hZy u
      omega
    apply Prod.ext
    · ext u
      have hz1 : x.1 u + x.2 u = Z u := congrFun hZx u
      have hz2 : y.1 u + y.2 u = Z u := congrFun hZy u
      have hxyu : x.2 u = y.2 u := congrFun hxy u
      omega
    · exact hxy
  have hcard : pre.card ≤ (subMsets A0).card :=
    Finset.card_le_card_of_injOn (fun x : (X → ℕ) × (X → ℕ) => x.2) hmap hinj
  have hcardA : (subMsets A0).card ≤ 2 ^ sizeM A0 := card_subMsets_le A0
  have hcardpow : (subMsets A0).card ≤ 2 ^ keyTotal k := by
    calc
      (subMsets A0).card ≤ 2 ^ sizeM A0 := hcardA
      _ = 2 ^ keyTotal k := by rw [hA0size]
  have hle1 : (∑ x ∈ pre, (∏ y : X, (((addM x.1 x.2) y).choose (x.2 y) : ℝ)))
      ≤ pre.card * (2 : ℝ) ^ keyTotal k := by
    calc
      (∑ x ∈ pre, (∏ y : X, (((addM x.1 x.2) y).choose (x.2 y) : ℝ)))
          ≤ ∑ x ∈ pre, (2 : ℝ) ^ keyTotal k := by
            apply Finset.sum_le_sum
            intro x hx
            have hxT : x ∈ fiberT N0 M hB k t := (Finset.mem_filter.mp hx).1
            have hxf : x ∈ fiber N0 M hB k := (Finset.mem_filter.mp hxT).1
            have hxpair : x ∈ pairSet N0 M hB := (Finset.mem_filter.mp hxf).1
            have hxkey : groupKey N0 hB x = k := (Finset.mem_filter.mp hxf).2
            have hb := pair_binom_le N0 M hB hxpair
            rwa [hxkey] at hb
      _ = pre.card * (2 : ℝ) ^ keyTotal k := by
            rw [Finset.sum_const, nsmul_eq_mul]
  have hle2 : pre.card * (2 : ℝ) ^ keyTotal k ≤ (2 : ℝ) ^ keyTotal k * (2 : ℝ) ^ keyTotal k := by
    have hc : (pre.card : ℝ) ≤ ((subMsets A0).card : ℝ) := by exact_mod_cast hcard
    have hc' : (pre.card : ℝ) ≤ (2 : ℝ) ^ keyTotal k := le_trans hc (by exact_mod_cast hcardpow)
    exact mul_le_mul_of_nonneg_right hc' (pow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) (keyTotal k))
  have hle3 : (2 : ℝ) ^ keyTotal k * (2 : ℝ) ^ keyTotal k = (2 : ℝ) ^ (2 * keyTotal k) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    (∑ x ∈ pre, (∏ y : X, (((addM x.1 x.2) y).choose (x.2 y) : ℝ)))
        ≤ pre.card * (2 : ℝ) ^ keyTotal k := hle1
    _ ≤ (2 : ℝ) ^ keyTotal k * (2 : ℝ) ^ keyTotal k := hle2
    _ = (2 : ℝ) ^ (2 * keyTotal k) := hle3

/-- fiber(k,t) with masses of Z on top: ≤ 2^{2n} · Σ_Z mass -/
lemma fiber_mass_binom_sum_le (N0 : MSys X) (M : ℕ) (hB : N0.LevelBounded)
    (μ : X → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (k : ℕ × (ℕ → ℕ)) (t : ℕ) :
    (∑ x ∈ fiberT N0 M hB k t,
        mass (M + t) μ (addM x.1 x.2) * (∏ y : X, (((addM x.1 x.2) y).choose (x.2 y) : ℝ)))
      ≤ (2 : ℝ) ^ (2 * keyTotal k) * (∑ Z ∈ msizeExact (X := X) (M + t), mass (M + t) μ Z) := by
  classical
  let S : Finset ((X → ℕ) × (X → ℕ)) := fiberT N0 M hB k t
  let P : (X → ℕ) × (X → ℕ) → ℝ := fun x =>
    ∏ y : X, (((addM x.1 x.2) y).choose (x.2 y) : ℝ)
  let Zf : (X → ℕ) × (X → ℕ) → X → ℕ := fun x => addM x.1 x.2
  have hmem : ∀ x ∈ S, Zf x ∈ msizeExact (X := X) (M + t) := by
    intro x hx
    have hxT : x ∈ fiberT N0 M hB k t := by simpa [S] using hx
    have hxT1 : x ∈ fiber N0 M hB k := (Finset.mem_filter.mp hxT).1
    have hxpair : x ∈ pairSet N0 M hB := (Finset.mem_filter.mp hxT1).1
    have hxt : sizeM x.2 = t := (Finset.mem_filter.mp hxT).2
    have hx1 : sizeM x.1 = M := pair_sizeM hxpair
    dsimp [Zf]
    apply mem_msizeExact
    rw [sizeM_add]
    rw [hx1, hxt]
  have hinner : ∀ Z ∈ msizeExact (X := X) (M + t),
      (∑ x ∈ S.filter (fun x => Zf x = Z), P x) ≤ (2 : ℝ) ^ (2 * keyTotal k) := by
    intro Z hZmem
    by_cases hne : (S.filter (fun x => Zf x = Z)).Nonempty
    · rcases hne with ⟨x0, hx0⟩
      have hx0S : x0 ∈ S := (Finset.mem_filter.mp hx0).1
      have hx0T : x0 ∈ fiberT N0 M hB k t := by simpa [S] using hx0S
      have hx0Z : Zf x0 = Z := (Finset.mem_filter.mp hx0).2
      have hb := fiber_Z_inner_le N0 M hB k t x0 hx0T
      have hx0Z' : addM x0.1 x0.2 = Z := by simpa [Zf] using hx0Z
      rw [hx0Z'] at hb
      simpa [S, Zf, P] using hb
    · have hfilt : S.filter (fun x => Zf x = Z) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro x hx hz
        exact hne ⟨x, Finset.mem_filter.mpr ⟨hx, hz⟩⟩
      rw [hfilt]
      simp
  calc
    (∑ x ∈ fiberT N0 M hB k t,
        mass (M + t) μ (addM x.1 x.2) * (∏ y : X, (((addM x.1 x.2) y).choose (x.2 y) : ℝ)))
        = ∑ x ∈ S, mass (M + t) μ (Zf x) * P x := rfl
    _ = ∑ Z ∈ msizeExact (X := X) (M + t),
          ∑ x ∈ S.filter (fun x => Zf x = Z), mass (M + t) μ (Zf x) * P x := by
          calc
            (∑ x ∈ S, mass (M + t) μ (Zf x) * P x)
                = ∑ x ∈ S, ∑ Z ∈ msizeExact (X := X) (M + t),
                    if Z = Zf x then mass (M + t) μ (Zf x) * P x else 0 := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    have hz := hmem x hx
                    have hsum := Finset.sum_ite_eq' (msizeExact (X := X) (M + t)) (Zf x)
                      (fun Z : X → ℕ => mass (M + t) μ (Zf x) * P x)
                    simpa [hz] using hsum.symm
            _ = ∑ Z ∈ msizeExact (X := X) (M + t),
                  ∑ x ∈ S, if Z = Zf x then mass (M + t) μ (Zf x) * P x else 0 := by
                  rw [Finset.sum_comm]
            _ = ∑ Z ∈ msizeExact (X := X) (M + t),
                  ∑ x ∈ S.filter (fun x => Zf x = Z), mass (M + t) μ (Zf x) * P x := by
                  apply Finset.sum_congr rfl
                  intro Z hZ
                  have hfs : S.filter (fun x => Z = Zf x) = S.filter (fun x => Zf x = Z) := by
                    ext x
                    simp [eq_comm]
                  calc
                    (∑ x ∈ S, if Z = Zf x then mass (M + t) μ (Zf x) * P x else 0)
                        = ∑ x ∈ S.filter (fun x => Z = Zf x), mass (M + t) μ (Zf x) * P x := by rw [Finset.sum_filter]
                    _ = ∑ x ∈ S.filter (fun x => Zf x = Z), mass (M + t) μ (Zf x) * P x := by rw [hfs]
    _ ≤ ∑ Z ∈ msizeExact (X := X) (M + t), mass (M + t) μ Z * (2 : ℝ) ^ (2 * keyTotal k) := by
          apply Finset.sum_le_sum
          intro Z hZmem
          have hmassZ : 0 ≤ mass (M + t) μ Z := mass_nonneg (M + t) hμ0 Z
          have hin := hinner Z hZmem
          calc
            (∑ x ∈ S.filter (fun x => Zf x = Z), mass (M + t) μ (Zf x) * P x)
                = mass (M + t) μ Z * (∑ x ∈ S.filter (fun x => Zf x = Z), P x) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro x hx
                  have hxZ : Zf x = Z := (Finset.mem_filter.mp hx).2
                  rw [hxZ]
            _ ≤ mass (M + t) μ Z * (2 : ℝ) ^ (2 * keyTotal k) :=
                  mul_le_mul_of_nonneg_left hin hmassZ
    _ = (2 : ℝ) ^ (2 * keyTotal k) * (∑ Z ∈ msizeExact (X := X) (M + t), mass (M + t) μ Z) := by
          calc
            (∑ Z ∈ msizeExact (X := X) (M + t), mass (M + t) μ Z * (2 : ℝ) ^ (2 * keyTotal k))
                = (∑ Z ∈ msizeExact (X := X) (M + t), mass (M + t) μ Z) * (2 : ℝ) ^ (2 * keyTotal k) := by
                  rw [← Finset.sum_mul]
            _ = (2 : ℝ) ^ (2 * keyTotal k) * (∑ Z ∈ msizeExact (X := X) (M + t), mass (M + t) μ Z) := by ring

/- ## Part 5: real power machinery and the fiber bound -/

lemma Kbig_pos : 0 < (Kbig : ℝ) := by
  exact_mod_cast (by norm_num [Kbig] : 0 < Kbig)

lemma ee_le_three : ee ≤ (3 : ℝ) := by
  unfold ee
  exact le_of_lt Real.exp_one_lt_three

lemma rhoVal_nonneg : 0 ≤ rhoVal := by
  unfold rhoVal
  exact div_nonneg (Real.exp_nonneg 1) (le_of_lt Kbig_pos)

lemma rhoVal_le_one : rhoVal ≤ 1 := by
  unfold rhoVal
  rw [div_le_one Kbig_pos]
  nlinarith [ee_le_three, (by norm_num [Kbig] : (3 : ℝ) ≤ (Kbig : ℝ))]

lemma zetaVal_nonneg : 0 ≤ zetaVal := by
  unfold zetaVal
  exact mul_nonneg (pow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) 3) (Real.sqrt_nonneg rhoVal)

/-- (a^n)^2 = (a^2)^n -/
lemma pow_sq (a : ℝ) (n : ℕ) : (a ^ n) ^ 2 = (a ^ 2) ^ n := by
  have h1 : (a ^ n) ^ 2 = a ^ (n * 2) := (pow_mul a n 2).symm
  rw [h1]
  have h2 : n * 2 = 2 * n := by omega
  rw [h2]
  exact pow_mul a 2 n

/-- for t ≥ n/2, rho^t ≤ (√rho)^n -/
lemma rho_pow_le_sqrt_pow (n t : ℕ) (h2t : n ≤ 2 * t) :
    rhoVal ^ t ≤ (Real.sqrt rhoVal) ^ n := by
  have hnon : 0 ≤ rhoVal := rhoVal_nonneg
  have hnon2 : 0 ≤ Real.sqrt rhoVal := Real.sqrt_nonneg rhoVal
  have hσ2 : (Real.sqrt rhoVal) ^ 2 = rhoVal := Real.sq_sqrt hnon
  have hs1 : rhoVal ≤ 1 := rhoVal_le_one
  have ha : 0 ≤ rhoVal ^ t := pow_nonneg hnon t
  have hb : 0 ≤ (Real.sqrt rhoVal) ^ n := pow_nonneg hnon2 n
  have h1 : (rhoVal ^ t) ^ 2 = rhoVal ^ (2 * t) := by
    calc
      (rhoVal ^ t) ^ 2 = (rhoVal ^ 2) ^ t := pow_sq rhoVal t
      _ = rhoVal ^ (2 * t) := by rw [← pow_mul]
  have h2 : ((Real.sqrt rhoVal) ^ n) ^ 2 = rhoVal ^ n := by
    rw [pow_sq]
    rw [hσ2]
  have hsq : (rhoVal ^ t) ^ 2 ≤ ((Real.sqrt rhoVal) ^ n) ^ 2 := by
    rw [h1, h2]
    exact pow_le_pow_of_le_one hnon hs1 (by omega : n ≤ 2 * t)
  have habs : |rhoVal ^ t| ≤ |(Real.sqrt rhoVal) ^ n| := by
    exact sq_le_sq.mp hsq
  rw [abs_of_nonneg ha, abs_of_nonneg hb] at habs
  exact habs

/-- M!/(M+t)! · (eN)^t ≤ rho^t  -/
lemma factorial_ratio_pow_le (N t : ℕ) :
    (Nat.factorial (Kbig * N) : ℝ) * (Nat.factorial (Kbig * N + t) : ℝ)⁻¹ * (eN N) ^ t
      ≤ rhoVal ^ t := by
  classical
  induction t with
  | zero =>
      rw [Nat.add_zero, pow_zero]
      have hne : (Nat.factorial (Kbig * N) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.factorial_ne_zero (Kbig * N))
      field_simp [hne]
      rfl
  | succ t ih =>
      let M : ℕ := Kbig * N
      have hpos0 : (0 : ℝ) < (Nat.factorial (M + t) : ℝ) := by
        exact_mod_cast (Nat.factorial_pos (M + t))
      have hpos1 : (0 : ℝ) < ((M + t + 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 0 < M + t + 1)
      have hrew : (Nat.factorial (M + (t + 1)) : ℝ)⁻¹ =
          (Nat.factorial (M + t) : ℝ)⁻¹ * (((M + t + 1 : ℕ) : ℝ)⁻¹) := by
        have hfac : Nat.factorial (M + (t + 1)) = (M + t + 1) * Nat.factorial (M + t) := by
          simpa [Nat.add_assoc, add_comm, add_left_comm] using (Nat.factorial_succ (M + t))
        have hc : (Nat.factorial (M + (t + 1)) : ℝ) =
            ((M + t + 1 : ℕ) : ℝ) * (Nat.factorial (M + t) : ℝ) := by
          exact_mod_cast hfac
        rw [hc]
        field_simp [hpos0.ne', hpos1.ne']
      have hratio : (eN N) * (((M + t + 1 : ℕ) : ℝ)⁻¹) ≤ rhoVal := by
        have hden : 0 < (((M + t + 1 : ℕ) : ℝ)) := by
          exact_mod_cast (by omega : 0 < M + t + 1)
        have hmain : (eN N) ≤ rhoVal * ((M + t + 1 : ℕ) : ℝ) := by
          have hposK : 0 < (Kbig : ℝ) := Kbig_pos
          have hcast : ((M + t + 1 : ℕ) : ℝ) = (Kbig : ℝ) * (N : ℝ) + (t : ℝ) + 1 := by
            dsimp [M]
            push_cast
            ring
          unfold rhoVal eN
          rw [hcast]
          have h1 : (ee / (Kbig : ℝ)) * ((Kbig : ℝ) * (N : ℝ) + (t : ℝ) + 1) =
              ee * (N : ℝ) + (ee / (Kbig : ℝ)) * ((t : ℝ) + 1) := by
            field_simp [hposK.ne']
            ring
          rw [h1]
          have hnonneg : 0 ≤ (ee / (Kbig : ℝ)) * ((t : ℝ) + 1) := by
            exact mul_nonneg (div_nonneg (Real.exp_nonneg 1) (le_of_lt hposK)) (by positivity)
          nlinarith
        exact (div_le_iff₀ hden).2 hmain
      calc
        (Nat.factorial M : ℝ) * (Nat.factorial (M + (t + 1)) : ℝ)⁻¹ * (eN N) ^ (t + 1)
            = (Nat.factorial M : ℝ) * ((Nat.factorial (M + t) : ℝ)⁻¹ * (((M + t + 1 : ℕ) : ℝ)⁻¹))
                * ((eN N) ^ t * (eN N)) := by
                rw [hrew]
                rw [pow_succ]
        _ = ((Nat.factorial M : ℝ) * (Nat.factorial (M + t) : ℝ)⁻¹ * (eN N) ^ t)
              * ((eN N) * (((M + t + 1 : ℕ) : ℝ)⁻¹)) := by ring
        _ ≤ rhoVal ^ t * ((eN N) * (((M + t + 1 : ℕ) : ℝ)⁻¹)) := by
              have hE : 0 ≤ eN N := by
                unfold eN
                exact mul_nonneg (Real.exp_nonneg 1) (by positivity)
              have hpos3 : 0 ≤ (eN N) * (((M + t + 1 : ℕ) : ℝ)⁻¹) :=
                mul_nonneg hE (by positivity)
              exact mul_le_mul_of_nonneg_right ih hpos3
        _ ≤ rhoVal ^ (t + 1) := by
              rw [pow_succ]
              exact mul_le_mul_of_nonneg_left hratio (pow_nonneg rhoVal_nonneg t)
        _ = rhoVal ^ (t + 1) := by ring

/-- mass identity for a pair with Z := W + U -/
lemma pair_mass_mul_cost (N0 : MSys X) (hB : N0.LevelBounded) (N : ℕ) (μ : X → ℝ)
    (k : ℕ × (ℕ → ℕ)) (t : ℕ) {x : (X → ℕ) × (X → ℕ)}
    (hx : x ∈ fiberT N0 (Kbig * N) hB k t) :
    mass (Kbig * N) μ x.1 * wCost (eN N) μ x.2
      = ((Nat.factorial (Kbig * N) : ℝ) * (Nat.factorial (Kbig * N + t) : ℝ)⁻¹ * (eN N) ^ t)
          * (mass (Kbig * N + t) μ (addM x.1 x.2)
              * (∏ y : X, (((addM x.1 x.2) y).choose (x.2 y) : ℝ))) := by
  classical
  have hxT1 : x ∈ fiber N0 (Kbig * N) hB k := (Finset.mem_filter.mp hx).1
  have hxpair : x ∈ pairSet N0 (Kbig * N) hB := (Finset.mem_filter.mp hxT1).1
  have ht : sizeM x.2 = t := (Finset.mem_filter.mp hx).2
  have hM : sizeM x.1 = Kbig * N := pair_sizeM hxpair
  have h1 := mass_mul_cost_eq (X := X) μ (addM x.1 x.2) x.2 (Kbig * N) t (eN N)
    (by intro y; unfold addM; omega)
    (by rw [sizeM_add, hM, ht])
    ht
  have hsub : subMM (addM x.1 x.2) x.2 = x.1 := by
    funext u
    unfold subMM addM
    omega
  rw [hsub] at h1
  rw [h1]
  ring

/-- mass sum over all Z is ≤ 1 -/
lemma mass_sum_le_one' (μ : X → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (hμle : (∑ x : X, μ x) ≤ 1)
    (L : ℕ) : (∑ Z ∈ msizeExact (X := X) L, mass L μ Z) ≤ 1 := mass_sum_le_one hμ0 hμle L

/-- per-(k,t) fiber bound: ≤ rho^t · 2^{2·keyTotal k} -/
lemma fiber_t_le (N0 : MSys X) (hB : N0.LevelBounded) (N : ℕ) (μ : X → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμle : (∑ x : X, μ x) ≤ 1)
    (k : ℕ × (ℕ → ℕ)) (t : ℕ) :
    (∑ x ∈ fiberT N0 (Kbig * N) hB k t, mass (Kbig * N) μ x.1 * wCost (eN N) μ x.2)
      ≤ rhoVal ^ t * (2 : ℝ) ^ (2 * keyTotal k) := by
  classical
  have hF : (Nat.factorial (Kbig * N) : ℝ) * (Nat.factorial (Kbig * N + t) : ℝ)⁻¹ * (eN N) ^ t
      ≤ rhoVal ^ t := factorial_ratio_pow_le N t
  have hsum : (∑ Z ∈ msizeExact (X := X) (Kbig * N + t), mass (Kbig * N + t) μ Z) ≤ 1 :=
    mass_sum_le_one' μ hμ0 hμle (Kbig * N + t)
  have hmass : (0 : ℝ) ≤ (∑ Z ∈ msizeExact (X := X) (Kbig * N + t), mass (Kbig * N + t) μ Z) := by
    exact Finset.sum_nonneg (by intro Z hZ; exact mass_nonneg (Kbig * N + t) hμ0 Z)
  have hmain : (∑ x ∈ fiberT N0 (Kbig * N) hB k t, mass (Kbig * N) μ x.1 * wCost (eN N) μ x.2)
      ≤ (Nat.factorial (Kbig * N) : ℝ) * (Nat.factorial (Kbig * N + t) : ℝ)⁻¹ * (eN N) ^ t
          * (2 : ℝ) ^ (2 * keyTotal k)
          * (∑ Z ∈ msizeExact (X := X) (Kbig * N + t), mass (Kbig * N + t) μ Z) := by
    calc
      (∑ x ∈ fiberT N0 (Kbig * N) hB k t, mass (Kbig * N) μ x.1 * wCost (eN N) μ x.2)
          = ∑ x ∈ fiberT N0 (Kbig * N) hB k t,
              ((Nat.factorial (Kbig * N) : ℝ) * (Nat.factorial (Kbig * N + t) : ℝ)⁻¹ * (eN N) ^ t)
                * (mass (Kbig * N + t) μ (addM x.1 x.2)
                    * (∏ y : X, (((addM x.1 x.2) y).choose (x.2 y) : ℝ))) := by
            apply Finset.sum_congr rfl
            intro x hx
            exact pair_mass_mul_cost N0 hB N μ k t hx
      _ = ((Nat.factorial (Kbig * N) : ℝ) * (Nat.factorial (Kbig * N + t) : ℝ)⁻¹ * (eN N) ^ t)
            * (∑ x ∈ fiberT N0 (Kbig * N) hB k t,
                mass (Kbig * N + t) μ (addM x.1 x.2)
                  * (∏ y : X, (((addM x.1 x.2) y).choose (x.2 y) : ℝ))) := by
            rw [← Finset.mul_sum]
      _ ≤ ((Nat.factorial (Kbig * N) : ℝ) * (Nat.factorial (Kbig * N + t) : ℝ)⁻¹ * (eN N) ^ t)
            * ((2 : ℝ) ^ (2 * keyTotal k) * (∑ Z ∈ msizeExact (X := X) (Kbig * N + t), mass (Kbig * N + t) μ Z)) := by
            have hfib := fiber_mass_binom_sum_le N0 (Kbig * N) hB μ hμ0 k t
            have hE : 0 ≤ eN N := by
              unfold eN
              exact mul_nonneg (Real.exp_nonneg 1) (by positivity)
            have hF0 : 0 ≤ (Nat.factorial (Kbig * N) : ℝ) * (Nat.factorial (Kbig * N + t) : ℝ)⁻¹ * (eN N) ^ t := by
              have hf1 : 0 ≤ (Nat.factorial (Kbig * N) : ℝ) := by exact_mod_cast (Nat.zero_le _)
              have hf2 : 0 ≤ (Nat.factorial (Kbig * N + t) : ℝ) := by exact_mod_cast (Nat.zero_le _)
              have h12 : 0 ≤ (Nat.factorial (Kbig * N) : ℝ) * (Nat.factorial (Kbig * N + t) : ℝ)⁻¹ :=
                mul_nonneg hf1 (inv_nonneg.mpr hf2)
              exact mul_nonneg h12 (pow_nonneg hE t)
            exact mul_le_mul_of_nonneg_left hfib hF0
      _ = ((Nat.factorial (Kbig * N) : ℝ) * (Nat.factorial (Kbig * N + t) : ℝ)⁻¹ * (eN N) ^ t)
            * (2 : ℝ) ^ (2 * keyTotal k) * (∑ Z ∈ msizeExact (X := X) (Kbig * N + t), mass (Kbig * N + t) μ Z) := by ring
  calc
    (∑ x ∈ fiberT N0 (Kbig * N) hB k t, mass (Kbig * N) μ x.1 * wCost (eN N) μ x.2)
        ≤ (Nat.factorial (Kbig * N) : ℝ) * (Nat.factorial (Kbig * N + t) : ℝ)⁻¹ * (eN N) ^ t
            * (2 : ℝ) ^ (2 * keyTotal k)
            * (∑ Z ∈ msizeExact (X := X) (Kbig * N + t), mass (Kbig * N + t) μ Z) := hmain
    _ ≤ rhoVal ^ t * (2 : ℝ) ^ (2 * keyTotal k) * (∑ Z ∈ msizeExact (X := X) (Kbig * N + t), mass (Kbig * N + t) μ Z) := by
          have h2 : 0 ≤ (2 : ℝ) ^ (2 * keyTotal k) := by positivity
          have h3 : 0 ≤ (∑ Z ∈ msizeExact (X := X) (Kbig * N + t), mass (Kbig * N + t) μ Z) := hmass
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hF h2) h3
    _ ≤ rhoVal ^ t * (2 : ℝ) ^ (2 * keyTotal k) * 1 := by
          have h2 : 0 ≤ rhoVal ^ t * (2 : ℝ) ^ (2 * keyTotal k) :=
            mul_nonneg (pow_nonneg rhoVal_nonneg t) (by positivity)
          exact mul_le_mul_of_nonneg_left hsum h2
    _ = rhoVal ^ t * (2 : ℝ) ^ (2 * keyTotal k) := by ring

/- ## Part 6: keys, aggregation, and the theorem -/

/-- sum of pair weights over one fiber -/
noncomputable def keyFiberSum (N0 : MSys X) (M : ℕ) (hB : N0.LevelBounded) (c : ℝ) (μ : X → ℝ)
    (k : ℕ × (ℕ → ℕ)) : ℝ :=
  ∑ x ∈ fiber N0 M hB k, mass M μ x.1 * wCost c μ x.2

/-- the set of group keys occurring -/
noncomputable def keySet (N0 : MSys X) (M : ℕ) (hB : N0.LevelBounded) : Finset (ℕ × (ℕ → ℕ)) :=
  (pairSet N0 M hB).image (fun x => groupKey N0 hB x)

/-- pairSum equals the sum over keys of the fiber sums -/
lemma pairSum_eq_keySum (N0 : MSys X) (M : ℕ) (hB : N0.LevelBounded) (c : ℝ) (μ : X → ℝ) :
    pairSum N0 M hB c μ = ∑ k ∈ keySet N0 M hB, keyFiberSum N0 M hB c μ k := by
  classical
  let v : (X → ℕ) × (X → ℕ) → ℝ := fun x => mass M μ x.1 * wCost c μ x.2
  have hkeymem (x : (X → ℕ) × (X → ℕ)) (hx : x ∈ pairSet N0 M hB) :
      groupKey N0 hB x ∈ keySet N0 M hB := by
    unfold keySet
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  calc
    pairSum N0 M hB c μ = ∑ x ∈ pairSet N0 M hB, v x := rfl
    _ = ∑ x ∈ pairSet N0 M hB,
          ∑ k ∈ keySet N0 M hB, if k = groupKey N0 hB x then v x else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          have hm := Finset.sum_ite_eq' (keySet N0 M hB) (groupKey N0 hB x) (fun k : ℕ × (ℕ → ℕ) => v x)
          have : (∑ k ∈ keySet N0 M hB, if k = groupKey N0 hB x then v x else 0) = v x := by
            simpa [hkeymem x hx] using hm
          exact this.symm
    _ = ∑ k ∈ keySet N0 M hB,
          ∑ x ∈ pairSet N0 M hB, if k = groupKey N0 hB x then v x else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ k ∈ keySet N0 M hB, keyFiberSum N0 M hB c μ k := by
          apply Finset.sum_congr rfl
          intro k hk
          have hfs : (pairSet N0 M hB).filter (fun x => k = groupKey N0 hB x) = fiber N0 M hB k := by
            ext x
            simp [fiber, eq_comm]
          calc
            (∑ x ∈ pairSet N0 M hB, if k = groupKey N0 hB x then v x else 0)
                = ∑ x ∈ (pairSet N0 M hB).filter (fun x => k = groupKey N0 hB x), v x := by rw [Finset.sum_filter]
            _ = ∑ x ∈ fiber N0 M hB k, v x := by rw [hfs]
            _ = keyFiberSum N0 M hB c μ k := rfl

/-- keyFiberSum splits over the admissible sizes t -/
lemma keyFiberSum_partition (N0 : MSys X) (M : ℕ) (hB : N0.LevelBounded) (c : ℝ) (μ : X → ℝ)
    (hTot : ∀ T ∈ N0.F, ((10 : ℝ) ^ 8)⁻¹ ≤ N0.totalWeightM T) (k : ℕ × (ℕ → ℕ)) :
    keyFiberSum N0 M hB c μ k
      = ∑ t ∈ fiberTs k, ∑ x ∈ fiberT N0 M hB k t, mass M μ x.1 * wCost c μ x.2 := by
  classical
  unfold keyFiberSum
  calc
    (∑ x ∈ fiber N0 M hB k, mass M μ x.1 * wCost c μ x.2)
        = ∑ t ∈ fiberTs k,
            ∑ x ∈ (fiber N0 M hB k).filter (fun x => sizeM x.2 = t), mass M μ x.1 * wCost c μ x.2 := by
            calc
              (∑ x ∈ fiber N0 M hB k, mass M μ x.1 * wCost c μ x.2)
                  = ∑ x ∈ fiber N0 M hB k,
                      (∑ t ∈ fiberTs k, if t = sizeM x.2 then mass M μ x.1 * wCost c μ x.2 else 0) := by
                      apply Finset.sum_congr rfl
                      intro x hx
                      have htin : sizeM x.2 ∈ fiberTs k := fiber_mem_Ts N0 M hB hx hTot
                      have hsum := Finset.sum_ite_eq' (fiberTs k) (sizeM x.2)
                        (fun t : ℕ => mass M μ x.1 * wCost c μ x.2)
                      simpa [htin] using hsum.symm
              _ = ∑ t ∈ fiberTs k,
                    ∑ x ∈ fiber N0 M hB k, if t = sizeM x.2 then mass M μ x.1 * wCost c μ x.2 else 0 := by
                    rw [Finset.sum_comm]
              _ = ∑ t ∈ fiberTs k,
                    ∑ x ∈ (fiber N0 M hB k).filter (fun x => sizeM x.2 = t),
                      mass M μ x.1 * wCost c μ x.2 := by
                    apply Finset.sum_congr rfl
                    intro t ht
                    have hfs : (fiber N0 M hB k).filter (fun x => t = sizeM x.2) =
                        (fiber N0 M hB k).filter (fun x => sizeM x.2 = t) := by
                      ext x
                      simp [eq_comm]
                    calc
                      (∑ x ∈ fiber N0 M hB k, if t = sizeM x.2 then mass M μ x.1 * wCost c μ x.2 else 0)
                          = ∑ x ∈ (fiber N0 M hB k).filter (fun x => t = sizeM x.2),
                              mass M μ x.1 * wCost c μ x.2 := by rw [Finset.sum_filter]
                      _ = ∑ x ∈ (fiber N0 M hB k).filter (fun x => sizeM x.2 = t),
                              mass M μ x.1 * wCost c μ x.2 := by rw [hfs]
    _ = ∑ t ∈ fiberTs k, ∑ x ∈ fiberT N0 M hB k t, mass M μ x.1 * wCost c μ x.2 := by
          unfold fiberT
          rfl

/-- per-key bound: fiber sum ≤ ζ^{keyTotal k} -/
lemma keyFiberSum_le (N0 : MSys X) (hB : N0.LevelBounded) (N : ℕ) (μ : X → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμle : (∑ x : X, μ x) ≤ 1)
    (hTot : ∀ T ∈ N0.F, ((10 : ℝ) ^ 8)⁻¹ ≤ N0.totalWeightM T)
    (k : ℕ × (ℕ → ℕ)) :
    keyFiberSum N0 (Kbig * N) hB (eN N) μ k ≤ zetaVal ^ keyTotal k := by
  classical
  let n : ℕ := keyTotal k
  have hpart : keyFiberSum N0 (Kbig * N) hB (eN N) μ k
      = ∑ t ∈ fiberTs k, ∑ x ∈ fiberT N0 (Kbig * N) hB k t,
          mass (Kbig * N) μ x.1 * wCost (eN N) μ x.2 :=
    keyFiberSum_partition N0 (Kbig * N) hB (eN N) μ hTot k
  have hts : fiberTs k ⊆ Finset.range (n + 1) := by
    intro t ht
    exact (Finset.mem_filter.mp ht).1
  have hcard : (fiberTs k).card ≤ n + 1 := by
    calc
      (fiberTs k).card ≤ (Finset.range (n + 1)).card := Finset.card_le_card hts
      _ = n + 1 := by simp
  have htle : ∀ t ∈ fiberTs k,
      (∑ x ∈ fiberT N0 (Kbig * N) hB k t, mass (Kbig * N) μ x.1 * wCost (eN N) μ x.2)
        ≤ rhoVal ^ t * (2 : ℝ) ^ (2 * n) := by
    intro t ht
    have hb := fiber_t_le N0 hB N μ hμ0 hμle k t
    simpa [n] using hb
  have hsqrt : ∀ t ∈ fiberTs k, rhoVal ^ t ≤ (Real.sqrt rhoVal) ^ n := by
    intro t ht
    have htge : (9 / 10 : ℝ) * (n : ℝ) ≤ (t : ℝ) := by
      simpa [n] using (Finset.mem_filter.mp ht).2
    have h2t : n ≤ 2 * t := by
      have h' : (n : ℝ) ≤ (2 : ℝ) * (t : ℝ) := by nlinarith
      exact_mod_cast h'
    exact rho_pow_le_sqrt_pow n t h2t
  have hmain : (∑ t ∈ fiberTs k,
        ∑ x ∈ fiberT N0 (Kbig * N) hB k t, mass (Kbig * N) μ x.1 * wCost (eN N) μ x.2)
      ≤ zetaVal ^ keyTotal k := by
    calc
      (∑ t ∈ fiberTs k, ∑ x ∈ fiberT N0 (Kbig * N) hB k t, mass (Kbig * N) μ x.1 * wCost (eN N) μ x.2)
          ≤ ∑ t ∈ fiberTs k, rhoVal ^ t * (2 : ℝ) ^ (2 * n) := by
            exact Finset.sum_le_sum (fun t ht => htle t ht)
      _ ≤ ∑ t ∈ fiberTs k, (Real.sqrt rhoVal) ^ n * (2 : ℝ) ^ (2 * n) := by
            exact Finset.sum_le_sum (fun t ht =>
              mul_le_mul_of_nonneg_right (hsqrt t ht) (by positivity))
      _ = (fiberTs k).card * ((Real.sqrt rhoVal) ^ n * (2 : ℝ) ^ (2 * n)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n + 1 : ℕ) * ((Real.sqrt rhoVal) ^ n * (2 : ℝ) ^ (2 * n)) := by
            have hc : ((fiberTs k).card : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) := by exact_mod_cast hcard
            exact mul_le_mul_of_nonneg_right hc (by positivity)
      _ ≤ (2 : ℝ) ^ n * ((Real.sqrt rhoVal) ^ n * (2 : ℝ) ^ (2 * n)) := by
            have h21 : (((n + 1 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ n := by exact_mod_cast (add_one_le_two_pow_nat n)
            exact mul_le_mul_of_nonneg_right h21 (by positivity)
      _ = zetaVal ^ keyTotal k := by
            have hpow2 : (2 : ℝ) ^ n * (2 : ℝ) ^ (2 * n) = (2 : ℝ) ^ (3 * n) := by
              rw [← pow_add]
              congr 1
              omega
            have hz : zetaVal ^ keyTotal k = (2 : ℝ) ^ (3 * n) * (Real.sqrt rhoVal) ^ n := by
              dsimp [zetaVal]
              calc
                zetaVal ^ keyTotal k = ((2 : ℝ) ^ 3 * Real.sqrt rhoVal) ^ keyTotal k := rfl
                _ = ((2 : ℝ) ^ 3) ^ keyTotal k * (Real.sqrt rhoVal) ^ keyTotal k := by rw [mul_pow]
                _ = (2 : ℝ) ^ (3 * keyTotal k) * (Real.sqrt rhoVal) ^ keyTotal k := by rw [← pow_mul]
                _ = (2 : ℝ) ^ (3 * n) * (Real.sqrt rhoVal) ^ n := by dsimp [n]
            calc
              (2 : ℝ) ^ n * ((Real.sqrt rhoVal) ^ n * (2 : ℝ) ^ (2 * n))
                  = (2 : ℝ) ^ n * (2 : ℝ) ^ (2 * n) * (Real.sqrt rhoVal) ^ n := by ring
              _ = (2 : ℝ) ^ (3 * n) * (Real.sqrt rhoVal) ^ n := by rw [hpow2]
              _ = zetaVal ^ keyTotal k := hz.symm
  rw [hpart]
  exact hmain

/-- each key in keySet is realised by a pair -/
lemma keySet_realized {N0 : MSys X} {M : ℕ} {hB : N0.LevelBounded} {k : ℕ × (ℕ → ℕ)}
    (hk : k ∈ keySet N0 M hB) :
    ∃ x : (X → ℕ) × (X → ℕ), x ∈ pairSet N0 M hB ∧ groupKey N0 hB x = k := by
  classical
  unfold keySet at hk
  exact (Finset.mem_image.mp hk)

/-- level of a key is at most τ -/
lemma keySet_level {N0 : MSys X} {M : ℕ} {hB : N0.LevelBounded} {k : ℕ × (ℕ → ℕ)}
    (hk : k ∈ keySet N0 M hB) : k.1 ≤ N0.τ := by
  classical
  rcases keySet_realized hk with ⟨x, hx, hk'⟩
  have hb : bOf N0 hB x = k.1 := congrArg Prod.fst hk'
  have hle := pair_b_le_tau N0 M hB hx
  rw [hb] at hle
  exact hle

/-- entries of a key are legal -/
lemma keySet_legal {N0 : MSys X} {M : ℕ} {hB : N0.LevelBounded} {k : ℕ × (ℕ → ℕ)}
    (hk : k ∈ keySet N0 M hB) (hLeg : N0.FLegalM) :
    ∀ j, j ≤ k.1 → Sel.Deep.Sys.LegalEntry (k.2 j) j := by
  classical
  intro j hj
  rcases keySet_realized hk with ⟨x, hx, hk'⟩
  have hprof : ∀ j, j ≤ k.1 → N0.sCount (pw N0 hB x) j = k.2 j := by
    intro j hj
    exact groupKey_profile N0 M hB x k hx hk' j hj
  have hj' : j ≤ N0.τ := le_trans hj (keySet_level hk)
  have hleg := pair_legal N0 M hB hLeg hx hj'
  rwa [← hprof j hj]

/-- top entry of a key is nonzero -/
lemma keySet_top {N0 : MSys X} {M : ℕ} {hB : N0.LevelBounded} {k : ℕ × (ℕ → ℕ)}
    (hk : k ∈ keySet N0 M hB) (hTot : ∀ T ∈ N0.F, ((10 : ℝ) ^ 8)⁻¹ ≤ N0.totalWeightM T) :
    k.2 k.1 ≠ 0 := by
  classical
  rcases keySet_realized hk with ⟨x, hx, hk'⟩
  have hsb := pair_sb_ne_zero N0 M hB hx hTot
  have hb : bOf N0 hB x = k.1 := congrArg Prod.fst hk'
  have hk2 : k.2 k.1 = N0.sCount (witness N0 hB x.1 x.2) (bOf N0 hB x) := by
    have hz := groupKey_profile N0 M hB x k hx hk' k.1 (by omega)
    rw [← hb] at hz
    rw [← hb]
    exact hz.symm
  rwa [hk2]

/-- entries of a key vanish above its level -/
lemma keySet_zero_above {N0 : MSys X} {M : ℕ} {hB : N0.LevelBounded} {k : ℕ × (ℕ → ℕ)}
    (hk : k ∈ keySet N0 M hB) : ∀ j, k.1 < j → k.2 j = 0 := by
  classical
  intro j hj
  rcases keySet_realized hk with ⟨x, hx, hk'⟩
  have hb : bOf N0 hB x = k.1 := congrArg Prod.fst hk'
  have hs : sOf N0 hB x j = k.2 j := by
    have hg := congrArg (fun q : ℕ × (ℕ → ℕ) => q.2 j) hk'
    simpa [groupKey] using hg
  unfold sOf at hs
  have hgt : ¬ j ≤ bOf N0 hB x := by
    rw [hb]
    omega
  rw [if_neg hgt] at hs
  exact hs.symm

/-- ζ := 8·√rho is at most 10^{-9} -/
lemma zetaVal_le : zetaVal ≤ ((10 : ℝ) ^ 9)⁻¹ := by
  have hz0 : 0 ≤ zetaVal := zetaVal_nonneg
  have hb0 : 0 ≤ ((10 : ℝ) ^ 9)⁻¹ := by positivity
  have hz2 : zetaVal ^ 2 = 64 * rhoVal := by
    unfold zetaVal
    rw [mul_pow, Real.sq_sqrt rhoVal_nonneg]
    norm_num
  have hsq : zetaVal ^ 2 ≤ (((10 : ℝ) ^ 9)⁻¹) ^ 2 := by
    rw [hz2]
    have hpow : (((10 : ℝ) ^ 9)⁻¹) ^ 2 = ((10 : ℝ) ^ 18)⁻¹ := by norm_num [← pow_mul]
    rw [hpow]
    have hmain : 64 * ee * ((10 : ℝ) ^ 70)⁻¹ ≤ ((10 : ℝ) ^ 18)⁻¹ := by
      have h1 : 64 * ee ≤ 64 * 3 := by nlinarith [ee_le_three]
      have h2 : 64 * 3 * ((10 : ℝ) ^ 70)⁻¹ ≤ ((10 : ℝ) ^ 18)⁻¹ := by
        field_simp [show ((10 : ℝ) ^ 70) ≠ 0 by positivity, show ((10 : ℝ) ^ 18) ≠ 0 by positivity]
        norm_num
      exact le_trans (mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ ((10 : ℝ) ^ 70)⁻¹)) h2
    calc
      64 * rhoVal = 64 * (ee * ((Kbig : ℝ)⁻¹)) := by
            unfold rhoVal
            rw [div_eq_mul_inv]
      _ = 64 * ee * ((Kbig : ℝ)⁻¹) := by ring
      _ = 64 * ee * (((10 : ℝ) ^ 70)⁻¹) := by
            congr 2
            have hK : (Kbig : ℝ) = (10 : ℝ) ^ 70 := by norm_num [Kbig]
            rw [hK]
      _ ≤ ((10 : ℝ) ^ 18)⁻¹ := hmain
  have habs : |zetaVal| ≤ |((10 : ℝ) ^ 9)⁻¹| := by
    exact sq_le_sq.mp hsq
  rw [abs_of_nonneg hz0, abs_of_nonneg hb0] at habs
  exact habs


theorem theorem_MLM (N : ℕ) (μ : X → ℝ) (N0 : MSys X)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμle : (∑ x : X, μ x) ≤ 1)
    (hB : N0.LevelBounded) (hTot : N0.TotBoundM) (hLeg : N0.FLegalM) :
    (∑ W ∈ badMsetsM N0 (Kbig * N),
        mass (X := X) (Kbig * N) μ W * coverCostEN N0 N μ W hB)
      ≤ (1 / 10 : ℝ) := by
  classical
  have h1 : (∑ W ∈ badMsetsM N0 (Kbig * N), mass (Kbig * N) μ W * coverCostEN N0 N μ W hB)
      = pairSum N0 (Kbig * N) hB (eN N) μ := by
    unfold coverCostEN coverCostM mTotalCost
    exact lhs_eq_pairSum N0 (Kbig * N) hB (eN N) μ
  have h2 : pairSum N0 (Kbig * N) hB (eN N) μ
      = ∑ k ∈ keySet N0 (Kbig * N) hB, keyFiberSum N0 (Kbig * N) hB (eN N) μ k :=
    pairSum_eq_keySum N0 (Kbig * N) hB (eN N) μ
  have h3 : (∑ k ∈ keySet N0 (Kbig * N) hB, keyFiberSum N0 (Kbig * N) hB (eN N) μ k)
      ≤ ∑ k ∈ keySet N0 (Kbig * N) hB, zetaVal ^ keyTotal k := by
    refine Finset.sum_le_sum ?_
    intro k hk
    exact keyFiberSum_le N0 hB N μ hμ0 hμle hTot k
  have hprof : (∑ k ∈ keySet N0 (Kbig * N) hB, zetaVal ^ keyTotal k) ≤ (10 : ℝ)⁻¹ := by
    exact ProfileSum.profile_sum_bound zetaVal zetaVal_nonneg zetaVal_le N0.τ (keySet N0 (Kbig * N) hB)
      (fun k hk => keySet_level (N0 := N0) (M := Kbig * N) (hB := hB) hk)
      (fun k hk => keySet_legal (N0 := N0) (M := Kbig * N) (hB := hB) hk hLeg)
      (fun k hk => keySet_top (N0 := N0) (M := Kbig * N) (hB := hB) hk hTot)
      (fun k hk => keySet_zero_above (N0 := N0) (M := Kbig * N) (hB := hB) hk)
  have hA : (∑ W ∈ badMsetsM N0 (Kbig * N), mass (Kbig * N) μ W * coverCostEN N0 N μ W hB)
      ≤ ∑ k ∈ keySet N0 (Kbig * N) hB, zetaVal ^ keyTotal k := by
    rw [h1, h2]
    exact h3
  have hB2 : (∑ k ∈ keySet N0 (Kbig * N) hB, zetaVal ^ keyTotal k) ≤ (1 / 10 : ℝ) := by
    simpa using hprof
  exact le_trans hA hB2

end MSys

end Multi
end Submission
