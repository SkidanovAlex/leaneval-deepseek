import Mathlib
import Submission.ChainTransport
import Submission.OChartChainJunction
import Submission.IntervalChainU

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 1600000

/-!
# Milestone-2 (iv) step 6, brick (b) — the chain alignment (shrinking)
slice: sub-pieces along which every transport lands forward

`ChainTransport.lean` (S111) proved the pure iterated-transport engine
over chains of aligned monotone pieces: its domain `ChainDomain
(q :: rest)` consists of the start parameters whose one-step transports
land in the subsequent pieces (`transports`), and its value
`chainValue` transports a start parameter through the whole chain
whenever that alignment condition holds.  The S106 shrinking slice proved
the elementary real-analysis shrink (`exists_interval_preimage_piece`: a
continuous real map on an open interval that sends a point into an open
target interval sends a whole interval neighbourhood of the point into
the target).  This module assembles the ALIGNMENT half of the chain
machinery — the construction that makes `transports` hold on genuine
whole sub-pieces rather than on a thin set of orbit points:

1. **sub-pieces** — `mono_restrict` (restricting a `MonotoneOnPiece` map
   to a sub-interval keeps the monotonicity), **`subMonoPiece`** (a piece
   `p` cut down to a sub-interval `(a,b)` of its interval, with the same
   coordinate map restricted; the `τ` of the sub-piece is the restriction
   of the `τ` of `p` — `subMonoPiece_τ`);
2. **lemma 1 — single-step shrinking** (`exists_subpiece_landing`): if
   the coordinate map of `p` sends a parameter `x₀` into the interval of
   the next piece `q` (`p.τ x₀ ∈ Ioo q.lo q.hi` — the one-step transport
   of `x₀` lands in `q`), then — `p.τ` being continuous — it sends a
   whole sub-piece of `p` around `x₀` into the interval of `q`: the
   S106 real shrink, packaged at the piece level with the sub-interval
   explicitly inside the domain of `p` (intersect the metric preimage
   ball with the domain interval around `x₀`);
3. **the correspondence relation** (`IsSubPiece`: `s` is `r` cut down to
   a sub-interval) and the recursive **forward-totality predicate**
   (`AlignedTotality`: from every element of every piece of the list, the
   transport through the remaining pieces is defined);
4. **lemmas 2 + 3 — backward-aligned sub-pieces**
   (`exists_aligned_subpieces`): given pieces `p :: rest` and a start
   parameter `x₀` of `p` whose full forward orbit through the chain
   exists (`htr : transports p rest x₀`), there are sub-pieces
   `sp :: qs` — `sp` a sub-piece of `p` containing `x₀`, the `qs`
   sub-pieces of the corresponding `rest` pieces in order
   (`List.Forall₂ IsSubPiece qs rest`) — along which **every transport
   lands forward**: `AlignedTotality (sp :: qs)` (every parameter of
   `sp`, and of every piece of `qs`, transports through the whole
   remainder of the aligned chain).  Built BACKWARDS from the last piece:
   the induction consumes the orbit one step at a time (`rcases htr`),
   recurses on the tail chain from the next orbit point, and pulls the
   next sub-piece's interval back through the current continuous
   coordinate map to a sub-piece around the current orbit point (lemma 1).

Honest framing (as at S106): the hypothesis `htr` (a full forward orbit)
is genuine data, not automatic — consecutive junction pieces sit at the
coordinates of classes that need not transport into one another, so an
alignment exists exactly when an orbit does (and the exhaustion must
supply the orbit); the value of this module is that whenever an orbit
exists, the transport extends from the single orbit to WHOLE sub-pieces
with forward totality — the interval-neighbourhood content the
exhaustion/ordering construction reads off.  The walk instantiation (the
walk pieces `walkJunctionPiece` of `IntervalCoverU.lean` are continuous,
so the `hcont` hypothesis is available) and the ℕ-family bridging for
`chain_transport_class_coordinate` are recorded in the ROADMAP as the
next slice.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

/-- Restricting a monotone-in-one-direction piece map to a sub-piece keeps
the monotonicity (the embedding `u ↦ ⟨(u : ℝ), hsub u.2⟩` preserves the
real order). -/
lemma mono_restrict {lo hi a b : ℝ} {f : ChartInterval lo hi → ℝ}
    (hf : MonotoneOnPiece f) (hsub : Set.Ioo a b ⊆ Set.Ioo lo hi) :
    MonotoneOnPiece (fun u : ChartInterval a b => f ⟨(u : ℝ), hsub u.2⟩) := by
  rcases hf with hfi | hfd
  · left
    intro x y hxy
    have hxy' : ((⟨(x : ℝ), hsub x.2⟩ : ChartInterval lo hi) : ℝ) <
        ((⟨(y : ℝ), hsub y.2⟩ : ChartInterval lo hi) : ℝ) := by
      simpa using hxy
    simpa using (hfi ⟨(x : ℝ), hsub x.2⟩ ⟨(y : ℝ), hsub y.2⟩ hxy')
  · right
    intro x y hxy
    have hxy' : ((⟨(x : ℝ), hsub x.2⟩ : ChartInterval lo hi) : ℝ) <
        ((⟨(y : ℝ), hsub y.2⟩ : ChartInterval lo hi) : ℝ) := by
      simpa using hxy
    simpa using (hfd ⟨(x : ℝ), hsub x.2⟩ ⟨(y : ℝ), hsub y.2⟩ hxy')

/-- The sub-piece of `p` over a sub-interval `(a,b)` of its interval: the
same coordinate map, restricted. -/
def subMonoPiece (p : MonoPiece) {a b : ℝ} (hsub : Set.Ioo a b ⊆ Set.Ioo p.lo p.hi) :
    MonoPiece where
  lo := a
  hi := b
  τ := fun u : ChartInterval a b => p.τ ⟨(u : ℝ), hsub u.2⟩
  hmono := mono_restrict p.hmono hsub

/-- The coordinate map of a sub-piece is the restriction of the original. -/
lemma subMonoPiece_τ {p : MonoPiece} {a b : ℝ} (hsub : Set.Ioo a b ⊆ Set.Ioo p.lo p.hi)
    (u : ChartInterval a b) :
    (subMonoPiece p hsub).τ u = p.τ ⟨(u : ℝ), hsub u.2⟩ := by
  rfl

/-- **Single-step shrinking (lemma 1).**  If the coordinate map of piece
`p` sends a parameter `x₀` into the interval of piece `q` (i.e. the
one-step transport of `x₀` lands in `q`), then — `p.τ` being continuous —
it sends a whole sub-piece of `p` around `x₀` into the interval of `q`:
the step-domain condition holds on a genuine interval neighbourhood of any
transport-aligned parameter. -/
lemma exists_subpiece_landing (p : MonoPiece) (q : MonoPiece)
    (hcont : Continuous p.τ) (x₀ : ChartInterval p.lo p.hi)
    (hx : p.τ x₀ ∈ Set.Ioo q.lo q.hi) :
    ∃ (a b : ℝ) (hsub : Set.Ioo a b ⊆ Set.Ioo p.lo p.hi),
      (x₀ : ℝ) ∈ Set.Ioo a b ∧
      ∀ u : ChartInterval a b, (subMonoPiece p hsub).τ u ∈ Set.Ioo q.lo q.hi := by
  rcases exists_interval_preimage_piece p.τ hcont x₀ hx with ⟨a₀, b₀, hab₀, hx₀a, hmap⟩
  let a : ℝ := max p.lo a₀
  let b : ℝ := min p.hi b₀
  have ha_lt : a < (x₀ : ℝ) := by
    rw [max_lt_iff]
    constructor
    · exact x₀.2.1
    · exact hx₀a.1
  have hlt_b : (x₀ : ℝ) < b := by
    rw [lt_min_iff]
    constructor
    · exact x₀.2.2
    · exact hx₀a.2
  have hsub₀ : Set.Ioo a b ⊆ Set.Ioo a₀ b₀ := by
    intro u hu
    constructor
    · exact lt_of_le_of_lt (le_max_right p.lo a₀) (by simpa [a] using hu.1)
    · exact lt_of_lt_of_le (by simpa [b] using hu.2) (min_le_right p.hi b₀)
  have hsubP : Set.Ioo a b ⊆ Set.Ioo p.lo p.hi := by
    intro u hu
    constructor
    · exact lt_of_le_of_lt (le_max_left p.lo a₀) (by simpa [a] using hu.1)
    · exact lt_of_lt_of_le (by simpa [b] using hu.2) (min_le_left p.hi b₀)
  refine ⟨a, b, hsubP, ⟨ha_lt, hlt_b⟩, ?_⟩
  · intro u
    have hu0 : (u : ℝ) ∈ Set.Ioo a₀ b₀ := hsub₀ u.2
    let emb : ChartInterval p.lo p.hi := ⟨(u : ℝ), hsubP u.2⟩
    have hv := hmap emb hu0
    simpa [emb, subMonoPiece] using hv

/-- A sub-piece correspondence: `s` is a sub-piece of `r` (same coordinate
map restricted to a sub-interval). -/
def IsSubPiece (s r : MonoPiece) : Prop :=
  ∃ hsub : Set.Ioo s.lo s.hi ⊆ Set.Ioo r.lo r.hi, s = subMonoPiece r hsub

/-- Pointwise forward totality along an aligned piece list: from every
element of every piece, the transport through the remaining pieces is
defined. -/
def AlignedTotality : List MonoPiece → Prop
  | [] => True
  | q :: rest => (∀ y : ChartInterval q.lo q.hi, transports q rest y) ∧ AlignedTotality rest

/-- **Backward-aligned sub-pieces (lemmas 2 + 3).**  Given pieces
`p :: rest` with a start parameter `x₀` of `p` whose one-step transports
land in the subsequent pieces (`htr`, i.e. `x₀` has a full forward orbit
through the chain), there are sub-pieces `sp :: qs` (`sp` a sub-piece of
`p` containing `x₀`; the `qs` sub-pieces of the corresponding `rest`
pieces, in order) along which every transport lands forward: every
parameter of `sp` (indeed of every piece of `sp :: qs`) transports
through the whole remainder of the aligned chain.  Built backwards from
the last piece: at each step the continuous coordinate map pulls the next
sub-piece's interval back to a sub-piece around the current orbit point. -/
theorem exists_aligned_subpieces : ∀ (rest : List MonoPiece) (p : MonoPiece),
    (∀ q : MonoPiece, q ∈ (p :: rest) → Continuous q.τ) →
    ∀ (x₀ : ChartInterval p.lo p.hi), transports p rest x₀ →
    ∃ sp : MonoPiece, ∃ qs : List MonoPiece,
      (∃ hsub : Set.Ioo sp.lo sp.hi ⊆ Set.Ioo p.lo p.hi, sp = subMonoPiece p hsub) ∧
      ((x₀ : ℝ) ∈ Set.Ioo sp.lo sp.hi) ∧
      AlignedTotality (sp :: qs) ∧
      List.Forall₂ IsSubPiece qs rest := by
  intro rest
  induction rest with
  | nil =>
      intro p hcont x₀ htr
      let hsubP : Set.Ioo p.lo p.hi ⊆ Set.Ioo p.lo p.hi := fun u hu => hu
      let sp : MonoPiece := subMonoPiece (a := p.lo) (b := p.hi) p hsubP
      refine ⟨sp, [], ?_, ?_, ?_, ?_⟩
      · refine ⟨hsubP, rfl⟩
      · change (x₀ : ℝ) ∈ Set.Ioo p.lo p.hi
        exact x₀.2
      · change (∀ y : ChartInterval sp.lo sp.hi, transports sp [] y) ∧ True
        constructor
        · intro y
          simp [transports]
        · trivial
      · exact List.Forall₂.nil
  | cons p' rest' ih =>
      intro p hcont x₀ htr
      rcases htr with ⟨h, htr'⟩
      let x₁ : ChartInterval p'.lo p'.hi := ⟨p.τ x₀, h⟩
      have hcont' : ∀ q : MonoPiece, q ∈ (p' :: rest') → Continuous q.τ := by
        intro q hq
        exact hcont q (by
          simp at hq ⊢
          rcases hq with hq | hq
          · right
            left
            exact hq
          · right
            right
            exact hq)
      rcases ih p' hcont' x₁ htr' with ⟨sp', qs', hsub', hx₁mem, htot', hcorr'⟩
      have hx1 : p.τ x₀ ∈ Set.Ioo sp'.lo sp'.hi := by
        simpa [x₁] using hx₁mem
      rcases exists_subpiece_landing p sp' (hcont p (by simp)) x₀ hx1 with
        ⟨a, b, hsub₀, hx₀mem, hland⟩
      let sp : MonoPiece := subMonoPiece p hsub₀
      refine ⟨sp, sp' :: qs', ?_, ?_, ?_, ?_⟩
      · refine ⟨hsub₀, rfl⟩
      · change (x₀ : ℝ) ∈ Set.Ioo a b
        exact hx₀mem
      · change (∀ y : ChartInterval sp.lo sp.hi, transports sp (sp' :: qs') y) ∧
          AlignedTotality (sp' :: qs')
        constructor
        · intro y
          have hland' : sp.τ y ∈ Set.Ioo sp'.lo sp'.hi := by
            change ((subMonoPiece p hsub₀).τ y) ∈ Set.Ioo sp'.lo sp'.hi
            simpa [subMonoPiece] using hland y
          refine ⟨hland', ?_⟩
          exact htot'.1 ⟨sp.τ y, hland'⟩
        · exact htot'
      · constructor
        · exact hsub'
        · exact hcorr'

/-! ## S125 opener — explicit sub-piece data (`SubDatum`) -/

/-- **Explicit sub-piece datum.**  For a piece `p`, an interval and the
embedding proof into `p`'s interval; the sub-piece is
`datumPiece d := subMonoPiece p d.sub` (with the interval endpoints `lo`,
`hi` carried explicitly), so its coordinate map is DEFINITIONALLY the
restriction of `p`'s — this is the explicit-data form that makes the
dependent `τ`-restriction equalities definitional (the S125 refactor: the
aligned family `q i := datumPiece (sub i)` has `(q i).τ` the restriction
of `(p i).τ` by `rfl`, dissolving the `MonoPiece.τ` dependent-rewrite
blocker of the `hsem` transfer). -/
structure SubDatum (p : MonoPiece) where
  lo : ℝ
  hi : ℝ
  sub : Set.Ioo lo hi ⊆ Set.Ioo p.lo p.hi

/-- The sub-piece determined by a datum (its coordinate map is the
restriction of the ambient piece's, definitionally). -/
def datumPiece {p : MonoPiece} (d : SubDatum p) : MonoPiece :=
  subMonoPiece (a := d.lo) (b := d.hi) p d.sub

/-- The interval of the datum sub-piece is the datum interval. -/
lemma datumPiece_lo {p : MonoPiece} (d : SubDatum p) : (datumPiece d).lo = d.lo := by
  rfl

/-- The interval of the datum sub-piece is the datum interval. -/
lemma datumPiece_hi {p : MonoPiece} (d : SubDatum p) : (datumPiece d).hi = d.hi := by
  rfl

/-- **The coordinate map of a datum sub-piece is the restriction of the
ambient piece's** (definitional — this is the `rfl`-level fact that makes
the `hsem` value-conjunct transfer work once the aligned family is built
from `SubDatum`s). -/
lemma datumPiece_τ {p : MonoPiece} (d : SubDatum p)
    (u : ChartInterval (datumPiece d).lo (datumPiece d).hi) :
    (datumPiece d).τ u = p.τ ⟨(u : ℝ), d.sub u.2⟩ := by
  rfl

/-- The datum sub-piece is a sub-piece of the ambient piece (the
correspondence is automatic from the datum). -/
lemma IsSubPiece_datumPiece {p : MonoPiece} (d : SubDatum p) : IsSubPiece (datumPiece d) p := by
  refine ⟨d.sub, ?_⟩
  rfl

/-- **Single-step data shrinking (lemma 1, datum form).**  If the
coordinate map of `p` sends a parameter into the next piece's interval,
then — `p.τ` continuous — a whole explicit datum sub-piece of `p` around
the parameter lands there: the `SubDatum` form of
`exists_subpiece_landing`, with the interval endpoints carried
explicitly. -/
lemma exists_subdata_landing (p : MonoPiece) (q : MonoPiece)
    (hcont : Continuous p.τ) (x₀ : ChartInterval p.lo p.hi)
    (hx : p.τ x₀ ∈ Set.Ioo q.lo q.hi) :
    ∃ d : SubDatum p, (x₀ : ℝ) ∈ Set.Ioo d.lo d.hi ∧
      ∀ u : ChartInterval (datumPiece d).lo (datumPiece d).hi,
        (datumPiece d).τ u ∈ Set.Ioo q.lo q.hi := by
  rcases exists_subpiece_landing p q hcont x₀ hx with ⟨a, b, hsub, hx₀mem, hland⟩
  refine ⟨{ lo := a, hi := b, sub := hsub }, hx₀mem, ?_⟩
  intro u
  have hu2 : (u : ℝ) ∈ Set.Ioo a b := by
    change (u : ℝ) ∈ Set.Ioo (datumPiece { lo := a, hi := b, sub := hsub }).lo
      (datumPiece { lo := a, hi := b, sub := hsub }).hi
    exact u.2
  have hv := hland ⟨(u : ℝ), hu2⟩
  simpa [datumPiece, subMonoPiece] using hv

/-! ## S126 — the data-alignment list (`SubDataFor`) and the
backward-aligned sub-data theorem (`exists_aligned_subdata`) -/

/-- The dependent data list aligned positionally with a piece list: for
`r :: rest` it carries a `SubDatum r` for the head and the data for
`rest`.  The aligned pieces are `datumPiece`s of the data (so their
coordinate maps are definitionally the restrictions of the ambient
pieces' — the S125 explicit-data form). -/
inductive SubDataFor : List MonoPiece → Type
  | nil : SubDataFor []
  | cons : {r : MonoPiece} → {rest : List MonoPiece} → SubDatum r → SubDataFor rest →
      SubDataFor (r :: rest)

/-- The aligned piece list built from data (positionally matching the
ambient list). -/
def datumPieces : {ps : List MonoPiece} → SubDataFor ps → List MonoPiece
  | [], SubDataFor.nil => []
  | _r :: _rest, SubDataFor.cons d tail => datumPiece d :: datumPieces tail

/-- The empty data list produces no pieces. -/
lemma datumPieces_nil : datumPieces (SubDataFor.nil : SubDataFor []) = [] := by
  rfl

/-- Forward totality along a data list: from every element of every datum
piece, the transport through the remaining datum pieces is defined. -/
def SubDataTotality : {ps : List MonoPiece} → SubDataFor ps → Prop
  | [], SubDataFor.nil => True
  | _r :: _rest, SubDataFor.cons d tail =>
      (∀ y : ChartInterval (datumPiece d).lo (datumPiece d).hi,
        transports (datumPiece d) (datumPieces tail) y) ∧ SubDataTotality tail

/-- **Backward-aligned sub-data.**  Given pieces `p :: rest` and a start
parameter `x₀` of `p` with a full forward orbit (`htr`), there are
explicit sub-piece data — a datum `d0` of `p` containing `x₀`, and the
tail data positionally aligned with `rest` — along which every transport
lands forward: every parameter of `datumPiece d0` (indeed of every datum
piece) transports through the whole remainder of the aligned chain.  The
`SubDatum` form of `exists_aligned_subpieces` (S121): the aligned pieces
are `datumPiece`s, so their τ-restrictions are definitional — the
foundation the S125 refactor needs for the `hsem` transfer. -/
theorem exists_aligned_subdata : ∀ (rest : List MonoPiece) (p : MonoPiece),
    (∀ q : MonoPiece, q ∈ (p :: rest) → Continuous q.τ) →
    ∀ (x₀ : ChartInterval p.lo p.hi), transports p rest x₀ →
    ∃ d0 : SubDatum p, ∃ tail : SubDataFor rest,
      ((x₀ : ℝ) ∈ Set.Ioo d0.lo d0.hi) ∧
      (∀ y : ChartInterval (datumPiece d0).lo (datumPiece d0).hi,
        transports (datumPiece d0) (datumPieces tail) y) ∧
      SubDataTotality tail := by
  intro rest
  induction rest with
  | nil =>
      intro p hcont x₀ htr
      let d0 : SubDatum p := { lo := p.lo, hi := p.hi, sub := (fun t ht => ht) }
      refine ⟨d0, SubDataFor.nil, ?_, ?_, ?_⟩
      · change (x₀ : ℝ) ∈ Set.Ioo p.lo p.hi
        exact x₀.2
      · intro y
        change transports (datumPiece d0) [] y
        simp [transports]
      · trivial
  | cons p' rest' ih =>
      intro p hcont x₀ htr
      rcases htr with ⟨h, htr'⟩
      let x₁ : ChartInterval p'.lo p'.hi := ⟨p.τ x₀, h⟩
      have hcont' : ∀ q : MonoPiece, q ∈ (p' :: rest') → Continuous q.τ := by
        intro q hq
        exact hcont q (by
          simp at hq ⊢
          rcases hq with hq | hq
          · right
            left
            exact hq
          · right
            right
            exact hq)
      rcases ih p' hcont' x₁ htr' with ⟨d0', tail', hx₁mem, hhead', htail'⟩
      have hx1 : p.τ x₀ ∈ Set.Ioo (datumPiece d0').lo (datumPiece d0').hi := by
        change p.τ x₀ ∈ Set.Ioo d0'.lo d0'.hi
        simpa [x₁] using hx₁mem
      rcases exists_subdata_landing p (datumPiece d0') (hcont p (by simp)) x₀ hx1 with
        ⟨d0, hx₀mem, hland⟩
      refine ⟨d0, SubDataFor.cons d0' tail', hx₀mem, ?_, ?_⟩
      · intro y
        have hmem : (datumPiece d0).τ y ∈ Set.Ioo (datumPiece d0').lo (datumPiece d0').hi :=
          hland y
        change transports (datumPiece d0) (datumPiece d0' :: datumPieces tail') y
        refine ⟨hmem, ?_⟩
        exact hhead' ⟨(datumPiece d0).τ y, hmem⟩
      · exact ⟨hhead', htail'⟩

/-! ## S134 — orbit extension at the pure level (`transports_extend`)

`chain_transport_class_coordinate` (S119) identifies the finite-chain
transport of the S111 engine with the genuine class coordinate whenever
the transport is defined.  What the exhaustion induction (`Uₙ`, S134)
still needs at the pure level is the EXTENSION principle: a parameter
whose transport through `n` tail pieces exists, whose chain value lands
in the NEXT piece `p (k+n+1)`, transports through `n+1` tail pieces
(the only new landing in the extended chain is the last one, supplied by
the chain value).  Proved by induction on `n` (`revert k` first so the IH
is `k`-parametrised); the step uses `htr.choose`/`htr.choose_spec`
directly (never `rcases htr`), so the chain-value recursion equation
closes by `rfl` (the chosen membership proof is already the one in the
recursion), and the index arithmetic is `k+(n+1)+1 = (k+1)+n+1`
(`omega`). -/
lemma transports_extend {p : ℕ → MonoPiece} : ∀ (k n : ℕ),
    ∀ (x : ChartInterval (p k).lo (p k).hi)
      (htr : transports (p k) (chainTail p k n) x),
      chainValue (p k :: chainTail p k n) ⟨x, htr⟩ ∈
          Set.Ioo (p (k + n + 1)).lo (p (k + n + 1)).hi →
      transports (p k) (chainTail p k (n + 1)) x := by
  intro k n
  revert k
  induction n with
  | zero =>
      intro k x htr hlast
      rw [show chainTail p k 1 = p (k + 1) :: chainTail p (k + 1) 0 by simp [chainTail]]
      have hmem : (p k).τ x ∈ Set.Ioo (p (k + 1)).lo (p (k + 1)).hi := by
        change chainValue (p k :: ([] : List MonoPiece)) ⟨x, htr⟩ ∈
          Set.Ioo (p (k + 1)).lo (p (k + 1)).hi
        simpa [chainTail] using hlast
      refine ⟨hmem, ?_⟩
      simp [transports, chainTail]
  | succ n ih =>
      intro k x htr hlast
      rw [show chainTail p k (n + 2) = p (k + 1) :: chainTail p (k + 1) (n + 1) by simp [chainTail]]
      refine ⟨htr.choose, ?_⟩
      apply ih (k + 1) ⟨(p k).τ x, htr.choose⟩ htr.choose_spec
      have hcv : chainValue (p (k + 1) :: chainTail p (k + 1) n)
            ⟨⟨(p k).τ x, htr.choose⟩, htr.choose_spec⟩ =
          chainValue (p k :: chainTail p k (n + 1)) ⟨x, htr⟩ := by
        rfl
      rw [hcv]
      rw [show (k + 1) + n + 1 = k + (n + 1) + 1 by omega]
      exact hlast

/-! ## S140c (piece level) — landing datum within a prescribed interval

The nesting of consecutive per-length cell charts (S140b `hI`) needs the
alignment's head datum to be chosen INSIDE the previous length's head
interval.  This is the pure piece-level shrink: given a landing datum
around `x₀` (S127 `exists_subdata_landing`) and a constraint datum `J`
whose interval also contains `x₀`, intersect the two intervals (both open
around `x₀`, so the intersection is a nonempty open interval) — the
resulting datum has its interval inside `J`'s and keeps the landing
property (inherited by subsets). -/

/-- **Landing datum within a prescribed interval.**  If the coordinate
map of `p` sends a parameter `x₀` into the interval of the next piece
`q` and `J` is a datum of `p` whose interval contains `x₀`, then there is
a datum `d` of `p` with `x₀` in its interval, its interval INSIDE `J`'s,
whose whole piece maps into `q`'s interval (intersect the S127 landing
datum with `J`; both contain `x₀`, so the intersection is a nonempty
open interval around `x₀`, and the landing property is inherited by
subsets). -/
lemma exists_subdata_landing_within (p : MonoPiece) (q : MonoPiece)
    (hcont : Continuous p.τ) (x₀ : ChartInterval p.lo p.hi)
    (hx : p.τ x₀ ∈ Set.Ioo q.lo q.hi) (J : SubDatum p)
    (hxJ : (x₀ : ℝ) ∈ Set.Ioo J.lo J.hi) :
    ∃ d : SubDatum p, (x₀ : ℝ) ∈ Set.Ioo d.lo d.hi ∧
      Set.Ioo d.lo d.hi ⊆ Set.Ioo J.lo J.hi ∧
      ∀ u : ChartInterval (datumPiece d).lo (datumPiece d).hi,
        (datumPiece d).τ u ∈ Set.Ioo q.lo q.hi := by
  rcases exists_subdata_landing p q hcont x₀ hx with ⟨d, hx₀mem, hland⟩
  have hmem : (x₀ : ℝ) ∈ Set.Ioo (max d.lo J.lo) (min d.hi J.hi) := by
    constructor
    · rw [max_lt_iff]
      exact ⟨hx₀mem.1, hxJ.1⟩
    · rw [lt_min_iff]
      exact ⟨hx₀mem.2, hxJ.2⟩
  have hsubD : Set.Ioo (max d.lo J.lo) (min d.hi J.hi) ⊆ Set.Ioo d.lo d.hi := by
    intro t ht
    constructor
    · exact lt_of_le_of_lt (le_max_left d.lo J.lo) ht.1
    · exact lt_of_lt_of_le ht.2 (min_le_left d.hi J.hi)
  have hsubJ : Set.Ioo (max d.lo J.lo) (min d.hi J.hi) ⊆ Set.Ioo J.lo J.hi := by
    intro t ht
    constructor
    · exact lt_of_le_of_lt (le_max_right d.lo J.lo) ht.1
    · exact lt_of_lt_of_le ht.2 (min_le_right d.hi J.hi)
  refine ⟨{ lo := max d.lo J.lo, hi := min d.hi J.hi, sub := fun t ht => d.sub (hsubD ht) },
    hmem, hsubJ, ?_⟩
  intro u
  have huD : (u : ℝ) ∈ Set.Ioo d.lo d.hi := hsubD u.2
  change (datumPiece d).τ ⟨(u : ℝ), huD⟩ ∈ Set.Ioo q.lo q.hi
  exact hland ⟨(u : ℝ), huD⟩


end LeanEval.KnotTheory.Quadrisecant
