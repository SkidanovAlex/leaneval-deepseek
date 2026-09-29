import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs
import Submission.Work.SynFFT.lvlAllGetD
import Submission.Work.SynFFT.lvlKit
import Submission.Work.SynFFT.lvlProg

/-!
# `Work.SynFFT.hasLvlPass`

`HasLvlPass` (one level pass on the whole slice): chunk the `t` coefficient vectors into blocks
of `m`, wrap each block with the five scalar parameters, apply the block word to every block
(in a fold), then reverse and flatten.

The program is `ifNil (push nil) (setup ; pairMap ; cleanup ; fold (block body) ; reverse ; flatten)`;
the `ifNil` test is needed because for `t = 0` the budget `K·0·(r+1)(p+1) + K = K` allows only a
constant number of steps.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace Work.SynFFT

open HvdH

local infixr:68 " ;;; " => HvdH.Cmd.seq

/-! ## Elementary size facts -/

theorem nat_size_le_self_xhasLvlPass (m : ℕ) : m.size ≤ m := Nat.size_le.mpr (Nat.lt_two_pow_self (n := m))

theorem isz_le_self_xhasLvlPass (z : ℤ) : isz z ≤ z.natAbs + 2 := by
  rw [isz]; exact Nat.add_le_add_right (nat_size_le_self_xhasLvlPass _) 2

theorem isz_natCast_le_xhasLvlPass (m : ℕ) : isz (m : ℤ) ≤ m + 2 := by
  have h := isz_le_self_xhasLvlPass (m : ℤ)
  rwa [Int.natAbs_natCast] at h

/-- `a ≤ a * X` for `X ≥ 1`. -/
theorem le_mul_of_one_le (a : ℕ) {X : ℕ} (hX : 1 ≤ X) : a ≤ a * X := by
  have := Nat.mul_le_mul_left a hX
  simpa using this

/-- `a ≤ X * a` for `X ≥ 1`. -/
theorem le_mul_of_one_le' (a : ℕ) {X : ℕ} (hX : 1 ≤ X) : a ≤ X * a := by
  have := Nat.mul_le_mul_right a hX
  simpa using this

/-- `1 ≤ a * b` for `a, b ≥ 1`. -/
theorem one_le_mul {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  simpa using Nat.mul_le_mul ha hb

theorem mul_le_mul3 {a b c a' b' c' : ℕ} (h1 : a ≤ a') (h2 : b ≤ b') (h3 : c ≤ c') :
    a * b * c ≤ a' * b' * c' := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3

/-- Every chunk of a slice of `t` in-disc coefficient vectors has value size
`≤ 15 (m+1)(r+1)(p+1)`. -/
theorem vsz_mem_chunkVals {m r p t : ℕ} {ws : List (List (ℤ × ℤ))}
    (hm : 1 ≤ m) (hlen : ws.length = t) (hdvd : m ∣ t) (hind : ∀ w ∈ ws, InDiscVec p r w) :
    ∀ x ∈ chunkVals m ws, vsz x ≤ 15 * (m + 1) * (r + 1) * (p + 1) := by
  intro x hx
  rw [chunkVals] at hx
  obtain ⟨b, hb, hxb⟩ := List.mem_map.mp hx
  rw [List.mem_range] at hb
  rw [← hxb]
  have hcx : List.take m (List.drop (b * m) (cvecs ws)) = cvecs (cws m ws b) :=
    cvecs_take_drop m ws b
  rw [hcx]
  refine @vsz_ofList_cvecs_le_xlvlProg m r p (cws m ws b) ?_ ?_
  · have hcl : (cvecs ws).length = t := by rw [cvecs, List.length_map, hlen]
    rw [hcl] at hb
    refine cws_length m ws ?_
    have := (Nat.le_div_iff_mul_le (show 0 < m by omega)).mp (Nat.succ_le_of_lt hb)
    rw [hlen]; exact this
  · intro w hw
    rw [cws] at hw
    exact hind w (List.Sublist.subset (List.drop_sublist (b * m) ws)
      (List.Sublist.subset (List.take_sublist m (ws.drop (b * m))) hw))

/-- The packed chunk list is small. -/
theorem vsz_chunkVals_le {m r p t : ℕ} {ws : List (List (ℤ × ℤ))} (hm : 1 ≤ m) (ht : 1 ≤ t)
    (hlen : ws.length = t) (hdvd : m ∣ t) (hind : ∀ w ∈ ws, InDiscVec p r w) :
    vsz (ofList (chunkVals m ws)) ≤ 40 * (t * (r + 1) * (p + 1)) := by
  have hlen' : (chunkVals m ws).length = t / m := by
    rw [chunkVals, List.length_map, List.length_range, cvecs, List.length_map, hlen]
  have h := MrgKit.vsz_ofList_le_of_bound (chunkVals m ws)
    (15 * (m + 1) * (r + 1) * (p + 1)) (t / m) (vsz_mem_chunkVals hm hlen hdvd hind)
    (le_of_eq hlen')
  -- h : vsz (ofList (chunkVals m ws)) ≤ t/m * (15*(m+1)*(r+1)*(p+1) + 1) + 1
  have hdiv : (t / m) * (m + 1) ≤ 2 * t := by
    have h1 : (t / m) * m ≤ t := Nat.div_mul_le_self t m
    have h2 : t / m ≤ t := Nat.div_le_self t m
    nlinarith [h1, h2]
  have hkey : (t / m) * (15 * (m + 1) * (r + 1) * (p + 1) + 1) + 1
      ≤ 40 * (t * (r + 1) * (p + 1)) := by
    have h3 : 15 * ((t / m) * (m + 1)) * ((r + 1) * (p + 1))
        ≤ 30 * (t * (r + 1) * (p + 1)) := by
      have h4 : 15 * ((t / m) * (m + 1)) * ((r + 1) * (p + 1))
          ≤ 15 * (2 * t) * ((r + 1) * (p + 1)) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 15 hdiv)
      have e : 15 * (2 * t) * ((r + 1) * (p + 1)) = 30 * (t * (r + 1) * (p + 1)) := by ring
      rwa [e] at h4
    have e1 : (t / m) * (15 * (m + 1) * (r + 1) * (p + 1) + 1) + 1
        = 15 * ((t / m) * (m + 1)) * ((r + 1) * (p + 1)) + (t / m) + 1 := by ring
    have h5 : t / m ≤ t := Nat.div_le_self t m
    have h6 : t ≤ t * (r + 1) * (p + 1) := by
      have h7 : (r + 1) * (p + 1) ≥ 1 := one_le_mul (by omega) (by omega)
      have h8 := Nat.mul_le_mul_left t h7
      simpa [mul_assoc] using h8
    have h9 : 1 ≤ t * (r + 1) * (p + 1) := by
      have h7 : 1 ≤ (r + 1) * (p + 1) := one_le_mul (by omega) (by omega)
      have h8 : 1 * ((r + 1) * (p + 1)) ≤ t * ((r + 1) * (p + 1)) := Nat.mul_le_mul_right _ ht
      calc (1 : ℕ) ≤ (r + 1) * (p + 1) := h7
        _ = 1 * ((r + 1) * (p + 1)) := by ring
        _ ≤ t * ((r + 1) * (p + 1)) := h8
        _ = t * (r + 1) * (p + 1) := by ring
    rw [e1]
    linarith [h3, h5, h6, h9]
  linarith [h, hkey]

/-- `pSz` is at most `20 (r+1)(p+1)`. -/
theorem pSz_le {m sh : ℕ} {sgn : ℤ} {r p : ℕ}
    (hm2 : 2 ≤ m) (hmr : m * 2 ^ sh = 2 * r) (hsgn : sgn = 1 ∨ sgn = -1) (hp : 2 * r < 2 ^ p) :
    pSz m sh sgn r p ≤ 20 * (r + 1) * (p + 1) := by
  have hmle : m ≤ 2 * r := by
    have h1 : m * 1 ≤ m * 2 ^ sh := Nat.mul_le_mul_left m Nat.one_le_two_pow
    rw [mul_one, hmr] at h1
    exact h1
  have hsh2 : 2 ^ sh ≤ r := by
    have h1 : 2 * 2 ^ sh ≤ m * 2 ^ sh := Nat.mul_le_mul_right (2 ^ sh) hm2
    rw [hmr] at h1
    exact Nat.le_of_mul_le_mul_left h1 (by norm_num)
  have hsh : sh ≤ r := le_trans (le_of_lt (Nat.lt_two_pow_self (n := sh))) hsh2
  have hgm : 2 * (r + 1) ≤ 2 * (r + 1) * (p + 1) := by
    have := Nat.mul_le_mul_left (2 * (r + 1)) (show 1 ≤ p + 1 by omega)
    simpa [mul_assoc] using this
  have hgr : 3 * (r + 1) ≤ 3 * (r + 1) * (p + 1) := by
    have := Nat.mul_le_mul_left (3 * (r + 1)) (show 1 ≤ p + 1 by omega)
    simpa [mul_assoc] using this
  have hgp : 3 * (p + 1) ≤ 3 * (r + 1) * (p + 1) := by
    have := Nat.mul_le_mul_right (3 * (p + 1)) (show 1 ≤ r + 1 by omega)
    simpa [mul_assoc, mul_comm, mul_left_comm] using this
  have h1 : isz (m : ℤ) ≤ 2 * (r + 1) * (p + 1) := by
    have := isz_natCast_le_xhasLvlPass m
    have h2 : m + 2 ≤ 2 * (r + 1) := by omega
    linarith [hgm]
  have h2 : isz (sh : ℤ) ≤ 3 * (r + 1) * (p + 1) := by
    have := isz_natCast_le_xhasLvlPass sh
    have h3 : sh + 2 ≤ 3 * (r + 1) := by omega
    linarith [hgr]
  have h3 : isz sgn ≤ 3 * (r + 1) * (p + 1) := by
    have h4 : sgn.natAbs = 1 := by rcases hsgn with h | h <;> simp [h]
    have := isz_le_self_xhasLvlPass sgn
    rw [h4] at this
    have : isz sgn ≤ 3 := by omega
    linarith [hgr]
  have h4 : isz (r : ℤ) ≤ 3 * (r + 1) * (p + 1) := by
    have := isz_natCast_le_xhasLvlPass r
    have h5 : r + 2 ≤ 3 * (r + 1) := by omega
    linarith [hgr]
  have h5 : isz (p : ℤ) ≤ 3 * (r + 1) * (p + 1) := by
    have := isz_natCast_le_xhasLvlPass p
    have h6 : p + 2 ≤ 3 * (p + 1) := by omega
    linarith [hgp]
  have h6 : 6 ≤ 6 * (r + 1) * (p + 1) := by
    have := Nat.mul_le_mul_left 6 (one_le_mul (by omega) (by omega) : 1 ≤ (r + 1) * (p + 1))
    simpa [mul_assoc] using this
  rw [pSz]
  linarith

/-- Every element of the second list of a `Forall₂` comes from an element of the first. -/
theorem forall₂_exists {α β : Type*} {P : α → β → Prop} {l₁ : List α} {l₂ : List β} {y : β}
    (h : List.Forall₂ P l₁ l₂) (hy : y ∈ l₂) : ∃ x ∈ l₁, P x y := by
  induction h with
  | nil => simp at hy
  | cons hab _ ih =>
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨_, by simp, hab⟩
    · obtain ⟨x, hx, hpx⟩ := ih hy
      exact ⟨x, List.mem_cons_of_mem _ hx, hpx⟩

theorem ofList_eq_nil_iff {l : List Val} : ofList l = Val.nil ↔ l = [] := by
  constructor
  · intro h
    cases l with
    | nil => rfl
    | cons a t =>
      have h' : Val.cons a (ofList t) = Val.nil := h
      exact absurd h' (fun hh => nomatch hh)
  · intro h; rw [h]; rfl

/-- Per-step budget times `X`. -/
theorem hasLvlPass (hk : Work.SynFFT.KLib) (hi : HvdH.IntLib) (hl : HvdH.LayoutLib) (hf : HvdH.FxLib)
    (hb : Work.SynFFT.HasBlkLvl) (hv : Work.SynFFT.LvlAllGetDProp) : Work.SynFFT.HasLvlPass := by
  obtain ⟨pickP, Kp, hpick⟩ := hk.pick
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  obtain ⟨pushP, Kpv, hpush⟩ := hk.pushVal
  obtain ⟨swP, Ksw, hsw⟩ := hk.swap
  obtain ⟨drP, Kdr, hdr⟩ := hk.drop
  obtain ⟨consP, Kcv, hcons⟩ := hk.consV
  obtain ⟨uncP, Kuc, hunc⟩ := hk.unconsV
  obtain ⟨mapP, Kml, hmap⟩ := hk.mapList
  obtain ⟨foldP, Kfl, hfold⟩ := hk.foldList
  obtain ⟨izP, Kiz, hiz⟩ := hk.ifNil
  obtain ⟨csP, Kcs, hcs⟩ := hl.chunksOf
  obtain ⟨revP, Krev, hrev⟩ := hl.reverse
  obtain ⟨fltP, Kflt, hflt⟩ := hl.flatten
  obtain ⟨blkP, Kb, hblk⟩ := hb
  set A : ℕ := Kp + Kcs + Kpv + Ksw + Kcv + Kdr + Kr + Kuc + Kb + Kml + Kfl + Kiz + Krev + Kflt
    with hA
  set B : ℕ := 10000000 * (A + 1) with hB
  set Kfin : ℕ := 100000000 * (A + 1) with hKfin
  have hKiz : Kiz ≤ Kfin := by rw [hKfin, hA]; omega
  have hB5 : 5 * B ≤ Kfin := by rw [hB, hKfin]; omega
  set qsetup : Cmd := (pickP 1 ;;; csP ;;; pickP 5 ;;; pickP 5 ;;; pickP 5 ;;; pickP 5 ;;; pickP 5 ;;;
    pushP .nil ;;; swP ;;; consP ;;; swP ;;; consP ;;; swP ;;; consP ;;; swP ;;; consP ;;; swP ;;; consP ;;;
    swP) with hqsetup
  set qpair : Cmd := mapP (pickP 1 ;;; rollP 1 ;;; consP) with hqpair
  set qclean : Cmd := (swP ;;; drP ;;; pushP .nil ;;; swP) with hqclean
  set qbody : Cmd := (lvlPre uncP rollP swP drP ;;; blkP ;;; lvlSuf rollP drP consP) with hqbody
  set qtail : Cmd := (foldP qbody ;;; revP ;;; fltP) with hqtail
  refine ⟨izP (pushP .nil) (qsetup ;;; qpair ;;; qclean ;;; qtail), Kfin, ?_⟩
  intro main p r t m sh sgn ws u e rest hm2 hdvd hmr hsgn hp hlen hind happ
  set Q : List Val → Prop := fun out => ∃ ws' : List (List (ℤ × ℤ)),
    out = ofList (cvecs ws') :: pM m sh sgn r p ++ rest ∧ ws'.length = t ∧
    (∀ w ∈ ws', InDiscVec p r w) ∧ ApproxSL p r t ws' (lvlN r m sgn u) (e + 1) with hQ
  have hpre : ∀ vs, vs = ofList (cvecs ws) :: .int (m:ℤ) :: .int (sh:ℤ) :: .int sgn ::
      .int (r:ℤ) :: .int (p:ℤ) :: rest → vs = ofList (cvecs ws) :: pM m sh sgn r p ++ rest := by
    intro vs hvs
    rw [hvs]
    simp only [pM, List.cons_append, List.nil_append]
  have hpost : ∀ out, Q out → ∃ ws' : List (List (ℤ × ℤ)),
      out = ofList (cvecs ws') :: .int (m:ℤ) :: .int (sh:ℤ) :: .int sgn ::
        .int (r:ℤ) :: .int (p:ℤ) :: rest ∧
      ws'.length = t ∧ (∀ w ∈ ws', InDiscVec p r w) ∧ ApproxSL p r t ws' (lvlN r m sgn u) (e + 1) := by
    intro out hout
    rw [hQ] at hout
    obtain ⟨ws', h1, h2, h3, h4⟩ := hout
    refine ⟨ws', ?_, h2, h3, h4⟩
    rw [h1]
    simp only [pM, List.cons_append, List.nil_append]
  rcases eq_or_ne (ofList (cvecs ws)) Val.nil with hvnil | hvnil
  · -- ## `t = 0`
    have hws : ws = [] := by
      have h1 : cvecs ws = [] := ofList_eq_nil_iff.mp hvnil
      have h2 : ws.length = 0 := by
        have := congrArg List.length h1
        simpa [cvecs] using this
      exact List.eq_nil_of_length_eq_zero h2
    have ht0 : t = 0 := by rw [← hlen, hws]; rfl
    have hpush1 : (ofList (cvecs ws) = Val.nil → WordR main (pushP .nil)
        (fun vs => vs = pM m sh sgn r p ++ rest) (fun _ out => Q out) (fun _ => Kpv * 2)) := by
      intro _
      refine MrgKit.WordR_weaken
        (pushStep2 (hpush main) .nil (pM m sh sgn r p ++ rest) (Kpv * 2)
          (by simp only [vsz_nil]; exact le_of_eq (by ring)))
        (fun _ h => h) (fun _ out _ hQ' => ?_) (fun _ _ => le_rfl)
      rw [hQ]
      refine ⟨[], ?_, ?_, ?_, ?_⟩
      · rw [hQ']; rfl
      · rw [ht0]; rfl
      · intro w hw; exact absurd hw (by simp)
      · rw [ht0]; exact ⟨rfl, by intro q hq; omega⟩
    have hpush2 : (ofList (cvecs ws) ≠ Val.nil →
        WordR main (qsetup ;;; qpair ;;; qclean ;;; qtail)
          (fun vs => vs = ofList (cvecs ws) :: pM m sh sgn r p ++ rest) (fun _ out => Q out)
          (fun _ => 0)) := fun hne => absurd hvnil hne
    refine MrgKit.WordR_weaken
      (hiz main (pushP .nil) (qsetup ;;; qpair ;;; qclean ;;; qtail) (ofList (cvecs ws))
        (pM m sh sgn r p ++ rest) Q Q (Kpv * 2) 0 hpush1 hpush2) hpre ?_ ?_
    · intro vs out _ hq
      exact hpost out (hq.1 hvnil)
    · intro vs _
      have hmax : max (Kpv * 2) 0 = Kpv * 2 := max_eq_left (by omega)
      have h2 : Kiz + Kpv * 2 ≤ Kfin := by rw [hKfin, hA]; omega
      rw [hmax, ht0]
      simp only [Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add]
      exact h2
  · -- ## `t ≥ 1`
    have ht1 : 1 ≤ t := by
      by_contra hc
      have ht0 : t = 0 := by omega
      have hws : ws = [] := by
        apply List.eq_nil_of_length_eq_zero
        rw [hlen, ht0]
      exact hvnil (by rw [hws]; rfl)
    have hm1 : 1 ≤ m := by omega
    have hcl : (cvecs ws).length = t := by rw [cvecs, List.length_map, hlen]
    have hdvd' : m ∣ (cvecs ws).length := by rw [hcl]; exact hdvd
    set X : ℕ := t * (r + 1) * (p + 1) with hX
    have hX1 : 1 ≤ X := by
      rw [hX]
      exact one_le_mul (one_le_mul ht1 (by omega)) (by omega)
    have htX : t ≤ X := by
      have h1 : 1 ≤ (r + 1) * (p + 1) := one_le_mul (by omega) (by omega)
      have h2 := Nat.mul_le_mul_left t h1
      rw [hX]; simpa [mul_assoc] using h2
    have hrp : (r + 1) * (p + 1) ≤ X := by
      have h2 := Nat.mul_le_mul_right ((r + 1) * (p + 1)) ht1
      rw [hX]; simpa [mul_assoc] using h2
    have hM1 : 1 ≤ (m + 1) * (r + 1) * (p + 1) :=
      one_le_mul (one_le_mul (by omega) (by omega)) (by omega)
    set BY : ℕ := B * X with hBY
    have hBY5 : 5 * BY ≤ Kfin * X := by
      rw [hBY, hB, hKfin]
      have h : 5 * (10000000 * (A + 1)) ≤ 100000000 * (A + 1) := by omega
      have h2 := Nat.mul_le_mul_right X h
      simpa [mul_assoc] using h2
    -- ### size atoms
    have hA1 : vsz (ofList (cvecs ws)) ≤ 30 * X := by
      have h := vsz_ofList_cvecs_le_xlvlProg (m := t) (r := r) (p := p) (w := ws) hlen hind
      have h4 := Nat.mul_le_mul_right ((r + 1) * (p + 1)) ht1
      have h3 : 15 * ((r + 1) * (p + 1)) ≤ 15 * (t * (r + 1) * (p + 1)) := by
        simpa [mul_assoc] using Nat.mul_le_mul_left 15 h4
      have e : 15 * (t + 1) * (r + 1) * (p + 1)
          = 15 * (t * (r + 1) * (p + 1)) + 15 * ((r + 1) * (p + 1)) := by ring
      rw [e] at h
      rw [hX]
      linarith
    have hA2 : vsz (ofList (chunkVals m ws)) ≤ 40 * X := by
      have h := vsz_chunkVals_le hm1 ht1 hlen hdvd hind
      rw [hX]; linarith
    have hPS20 : pSz m sh sgn r p ≤ 20 * (r + 1) * (p + 1) := pSz_le hm2 hmr hsgn hp
    have hPSr : pSz m sh sgn r p ≤ 20 * ((r + 1) * (p + 1)) := by
      have e : 20 * (r + 1) * (p + 1) = 20 * ((r + 1) * (p + 1)) := by ring
      rwa [e] at hPS20
    have hPS : pSz m sh sgn r p ≤ 20 * X := by
      have h3 : 20 * ((r + 1) * (p + 1)) ≤ 20 * X := Nat.mul_le_mul_left 20 hrp
      linarith
    have hm2r : m ≤ 2 * r := by
      have h1 : m * 1 ≤ m * 2 ^ sh := Nat.mul_le_mul_left m Nat.one_le_two_pow
      rwa [mul_one, hmr] at h1
    have hIM4 : isz (m : ℤ) ≤ 4 * ((r + 1) * (p + 1)) := by
      have h := isz_natCast_le_xhasLvlPass m
      have h2 : m + 2 ≤ 2 * (r + 1) := by omega
      have h4 : (r + 1) ≤ (r + 1) * (p + 1) := le_mul_of_one_le _ (by omega)
      have h3 : 2 * (r + 1) ≤ 2 * ((r + 1) * (p + 1)) := Nat.mul_le_mul_left 2 h4
      linarith
    have hIM : isz (m : ℤ) ≤ 4 * X := by
      have h3 : 4 * ((r + 1) * (p + 1)) ≤ 4 * X := Nat.mul_le_mul_left 4 hrp
      linarith
    have hTM : (cvecs ws).length / m + 1 ≤ 2 * t := by
      rw [hcl]
      have := Nat.div_le_self t m
      omega
    have hTMIM : ((cvecs ws).length / m + 1) * isz (m : ℤ) ≤ 8 * X := by
      have h := Nat.mul_le_mul hTM hIM4
      have e : 2 * t * (4 * ((r + 1) * (p + 1))) = 8 * X := by rw [hX]; ring
      rw [e] at h
      exact h
    have hLch : ∀ x ∈ chunkVals m ws, vsz x ≤ 15 * (m + 1) * (r + 1) * (p + 1) :=
      vsz_mem_chunkVals hm1 hlen hdvd hind
    have hpszm : pSz m sh sgn r p ≤ 20 * ((m + 1) * (r + 1) * (p + 1)) := by
      have h4 : (r + 1) * (p + 1) ≤ (r + 1) * (p + 1) * (m + 1) :=
        le_mul_of_one_le _ (by omega)
      have h5 : 20 * ((r + 1) * (p + 1)) ≤ 20 * ((r + 1) * (p + 1) * (m + 1)) :=
        Nat.mul_le_mul_left 20 h4
      linarith [hPSr, h5]
    have hclen : (chunkVals m ws).length = t / m := by
      rw [chunkVals, List.length_map, List.length_range, hcl]
    have hLm : (t / m) * (m + 1) ≤ 2 * t := by
      have h1 : (t / m) * (m + 1) = (t / m) * m + (t / m) := by ring
      rw [h1]
      have h2 := Nat.div_mul_le_self t m
      have h3 := Nat.div_le_self t m
      omega
    have hTM1 : (t / m) * ((m + 1) * (r + 1) * (p + 1)) ≤ 2 * X := by
      have h3 := Nat.mul_le_mul_right ((r + 1) * (p + 1)) hLm
      have e : (t / m) * ((m + 1) * (r + 1) * (p + 1))
          = (t / m) * (m + 1) * ((r + 1) * (p + 1)) := by ring
      have e2 : 2 * t * ((r + 1) * (p + 1)) = 2 * X := by rw [hX]; ring
      rw [← e, e2] at h3
      exact h3
    have htmX : (t / m) ≤ X := le_trans (Nat.div_le_self t m) htX
    have hLch1 : 15 * (m + 1) * (r + 1) * (p + 1) + pSz m sh sgn r p + 1
        ≤ 40 * ((m + 1) * (r + 1) * (p + 1)) := by
      linarith [hpszm, hM1]
    have hLch2 : 15 * (m + 1) * (r + 1) * (p + 1) + pSz m sh sgn r p + 2
        ≤ 42 * ((m + 1) * (r + 1) * (p + 1)) := by
      linarith [hpszm, hM1]
    have hX80 : (t / m) * (15 * (m + 1) * (r + 1) * (p + 1) + pSz m sh sgn r p + 1)
        ≤ 80 * X := by
      have h5 := Nat.mul_le_mul_left (t / m) hLch1
      have h6 : (t / m) * (40 * ((m + 1) * (r + 1) * (p + 1))) ≤ 40 * (2 * X) := by
        have e : (t / m) * (40 * ((m + 1) * (r + 1) * (p + 1)))
            = 40 * ((t / m) * ((m + 1) * (r + 1) * (p + 1))) := by ring
        rw [e]
        exact Nat.mul_le_mul_left 40 hTM1
      have e3 : 40 * (2 * X) = 80 * X := by ring
      rw [e3] at h6
      linarith
    have hX84 : (t / m) * (15 * (m + 1) * (r + 1) * (p + 1) + pSz m sh sgn r p + 2)
        ≤ 84 * X := by
      have h5 := Nat.mul_le_mul_left (t / m) hLch2
      have h6 : (t / m) * (42 * ((m + 1) * (r + 1) * (p + 1))) ≤ 42 * (2 * X) := by
        have e : (t / m) * (42 * ((m + 1) * (r + 1) * (p + 1)))
            = 42 * ((t / m) * ((m + 1) * (r + 1) * (p + 1))) := by ring
        rw [e]
        exact Nat.mul_le_mul_left 42 hTM1
      have e3 : 42 * (2 * X) = 84 * X := by ring
      rw [e3] at h6
      linarith
    -- ### the setup step
    have hs : WordR main qsetup
        (fun vs => vs = ofList (cvecs ws) :: pM m sh sgn r p ++ rest)
        (fun _ out => out = ofList (chunkVals m ws) :: prepVR m sh sgn r p ::
          pM m sh sgn r p ++ rest)
        (fun _ => BY) := by
      rw [hqsetup]
      refine MrgKit.WordR_weaken
        (lvlSetup (hpick main) (hcs main) (hpush main) (hsw main) (hcons main)
          m sh sgn r p ws rest hm1 hdvd')
        (fun _ h => h) (fun _ _ _ h => h) (fun _ _ => ?_)
      have h1 : vsz (ofList (cvecs ws)) + isz (m : ℤ) + 1 ≤ 35 * X := by
        linarith [hA1, hIM, hX1]
      have h2 : vsz (ofList (cvecs ws)) + ((cvecs ws).length / m + 1) * isz (m : ℤ) + 1
          ≤ 39 * X := by linarith [hA1, hTMIM, hX1]
      have h3 : vsz (ofList (chunkVals m ws)) + pSz m sh sgn r p + 1 ≤ 61 * X := by
        linarith [hA2, hPS, hX1]
      have h4 : 4 * pSz m sh sgn r p + 8 ≤ 88 * X := by linarith [hPS, hX1]
      have t1 : Kp * 2 * (vsz (ofList (cvecs ws)) + isz (m : ℤ) + 1) ≤ Kp * 2 * (35 * X) :=
        Nat.mul_le_mul_left _ h1
      have t2 : Kcs * (vsz (ofList (cvecs ws)) + ((cvecs ws).length / m + 1) * isz (m : ℤ) + 1)
          ≤ Kcs * (39 * X) := Nat.mul_le_mul_left _ h2
      have t3 : 5 * (Kp * 6 * (vsz (ofList (chunkVals m ws)) + pSz m sh sgn r p + 1))
          ≤ 5 * (Kp * 6 * (61 * X)) :=
        Nat.mul_le_mul_left 5 (Nat.mul_le_mul_left (Kp * 6) h3)
      have t4 : Kpv * 2 ≤ Kpv * 2 * X := le_mul_of_one_le _ hX1
      have t5 : 5 * (Ksw * (4 * pSz m sh sgn r p + 8) + Kcv)
          ≤ 5 * (Ksw * (88 * X) + Kcv * X) := by
        have h5 : Ksw * (4 * pSz m sh sgn r p + 8) ≤ Ksw * (88 * X) := Nat.mul_le_mul_left _ h4
        have h6 : Kcv ≤ Kcv * X := le_mul_of_one_le _ hX1
        linarith
      have t6 : Ksw * (vsz (ofList (chunkVals m ws)) + pSz m sh sgn r p + 1) ≤ Ksw * (61 * X) :=
        Nat.mul_le_mul_left _ h3
      rw [lvlSetupCost, hBY]
      have hcoef : 70 * Kp + 39 * Kcs + 1830 * Kp + 2 * Kpv + 440 * Ksw + 5 * Kcv + 61 * Ksw
          ≤ B := by rw [hB, hA]; omega
      have hx := Nat.mul_le_mul_right X hcoef
      linarith [t1, t2, t3, t4, t5, t6, hx]
    -- ### the pairing step
    have hpair : WordR main qpair
        (fun vs => vs = ofList (chunkVals m ws) :: prepVR m sh sgn r p :: pM m sh sgn r p ++ rest)
        (fun _ out => ∃ ys, out = ofList ys :: prepVR m sh sgn r p :: pM m sh sgn r p ++ rest ∧
          List.Forall₂ (fun x y => y = .cons x (prepVR m sh sgn r p)) (chunkVals m ws) ys)
        (fun _ => BY) := by
      rw [hqpair]
      refine MrgKit.WordR_weaken
        (lvlPairMap (hpick main) (hroll main) (hcons main) (hmap main) m sh sgn r p ws rest
          (15 * (m + 1) * (r + 1) * (p + 1)) hLch)
        (fun _ h => h) (fun _ _ _ h => h) (fun _ _ => ?_)
      have t1 : (t / m) * (Kp * 2 * (15 * (m + 1) * (r + 1) * (p + 1) + pSz m sh sgn r p + 1))
          ≤ Kp * 2 * (80 * X) := by
        calc (t / m) * (Kp * 2 * (15 * (m + 1) * (r + 1) * (p + 1) + pSz m sh sgn r p + 1))
            = Kp * 2 * ((t / m) * (15 * (m + 1) * (r + 1) * (p + 1) + pSz m sh sgn r p + 1)) := by ring
          _ ≤ Kp * 2 * (80 * X) := Nat.mul_le_mul_left _ hX80
      have t2 : (t / m) * (Kr * 2 * (15 * (m + 1) * (r + 1) * (p + 1) + pSz m sh sgn r p + 1))
          ≤ Kr * 2 * (80 * X) := by
        calc (t / m) * (Kr * 2 * (15 * (m + 1) * (r + 1) * (p + 1) + pSz m sh sgn r p + 1))
            = Kr * 2 * ((t / m) * (15 * (m + 1) * (r + 1) * (p + 1) + pSz m sh sgn r p + 1)) := by ring
          _ ≤ Kr * 2 * (80 * X) := Nat.mul_le_mul_left _ hX80
      have t3 : (t / m) * Kcv ≤ Kcv * X := by
        calc (t / m) * Kcv ≤ X * Kcv := Nat.mul_le_mul_right Kcv htmX
          _ = Kcv * X := by ring
      have t4 : (t / m) * (Kml * (15 * (m + 1) * (r + 1) * (p + 1) + pSz m sh sgn r p + 2))
          ≤ Kml * (84 * X) := by
        calc (t / m) * (Kml * (15 * (m + 1) * (r + 1) * (p + 1) + pSz m sh sgn r p + 2))
            = Kml * ((t / m) * (15 * (m + 1) * (r + 1) * (p + 1) + pSz m sh sgn r p + 2)) := by ring
          _ ≤ Kml * (84 * X) := Nat.mul_le_mul_left _ hX84
      have t5 : Kml ≤ Kml * X := le_mul_of_one_le _ hX1
      rw [hBY, hclen]
      have hcoef : 160 * Kp + 160 * Kr + Kcv + 84 * Kml + Kml ≤ B := by rw [hB, hA]; omega
      have hx := Nat.mul_le_mul_right X hcoef
      linarith [t1, t2, t3, t4, t5, hx]
    -- ### the per-element tail: cleanup ; fold ; teardown
    have hrest : ∀ (ys : List Val),
        List.Forall₂ (fun x y => y = .cons x (prepVR m sh sgn r p)) (chunkVals m ws) ys →
        WordR main (qclean ;;; qtail)
          (fun vs => vs = ofList ys :: prepVR m sh sgn r p :: pM m sh sgn r p ++ rest)
          (fun _ out => Q out) (fun _ => BY + (BY + BY)) := by
      intro ys hF
      have hyclen : ys.length = t / m := by
        have h := hF.length_eq
        rw [← h, hclen]
      have hysv : vsz (ofList ys) ≤ 100 * X := by
        have hb1 : ∀ y ∈ ys, vsz y ≤ 15 * (m + 1) * (r + 1) * (p + 1) + pSz m sh sgn r p + 1 := by
          intro y hy
          obtain ⟨x, hx, rfl⟩ := forall₂_exists hF hy
          have hx1 : vsz x ≤ 15 * (m + 1) * (r + 1) * (p + 1) := hLch x hx
          have hpv : vsz (prepVR m sh sgn r p) ≤ pSz m sh sgn r p := vsz_prepVR m sh sgn r p
          rw [MrgKit.vsz_cons']
          omega
        have hbb : vsz (ofList ys) ≤ (t / m) * (15 * (m + 1) * (r + 1) * (p + 1)
            + pSz m sh sgn r p + 2) + 1 :=
          MrgKit.vsz_ofList_le_of_bound ys (15 * (m + 1) * (r + 1) * (p + 1)
            + pSz m sh sgn r p + 1) (t / m) hb1 (le_of_eq hyclen)
        have h5 := Nat.mul_le_mul_left (t / m) hLch2
        have h6 : (t / m) * (42 * ((m + 1) * (r + 1) * (p + 1))) ≤ 42 * (2 * X) := by
          have e : (t / m) * (42 * ((m + 1) * (r + 1) * (p + 1)))
              = 42 * ((t / m) * ((m + 1) * (r + 1) * (p + 1))) := by ring
          rw [e]
          exact Nat.mul_le_mul_left 42 hTM1
        have e3 : 42 * (2 * X) = 84 * X := by ring
        rw [e3] at h6
        linarith [hbb, h5, h6, hX1]
      have hcl' : WordR main qclean
          (fun vs => vs = ofList ys :: prepVR m sh sgn r p :: pM m sh sgn r p ++ rest)
          (fun _ out => out = ofList ys :: .nil :: pM m sh sgn r p ++ rest) (fun _ => BY) := by
        rw [hqclean]
        refine MrgKit.WordR_weaken
          (lvlCleanup (hsw main) (hdr main) (hpush main) m sh sgn r p rest ys)
          (fun _ h => h) (fun _ _ _ h => h) (fun _ _ => ?_)
        have hpv : vsz (prepVR m sh sgn r p) ≤ 20 * X := by
          have h := vsz_prepVR m sh sgn r p
          linarith [hPS]
        have t1 : Ksw * (vsz (ofList ys) + vsz (prepVR m sh sgn r p) + 1) ≤ Ksw * (121 * X) :=
          Nat.mul_le_mul_left _ (by linarith [hysv, hpv, hX1])
        have t2 : Kdr * (vsz (prepVR m sh sgn r p) + 1) ≤ Kdr * (21 * X) :=
          Nat.mul_le_mul_left _ (by linarith [hpv, hX1])
        have t3 : Kpv * 2 ≤ Kpv * 2 * X := le_mul_of_one_le _ hX1
        have t4 : Ksw * (vsz (ofList ys) + 1 + 1) ≤ Ksw * (102 * X) :=
          Nat.mul_le_mul_left _ (by linarith [hysv, hX1])
        rw [hBY]
        have hcoef : 121 * Ksw + 21 * Kdr + 2 * Kpv + 102 * Ksw ≤ B := by rw [hB, hA]; omega
        have hx := Nat.mul_le_mul_right X hcoef
        linarith [t1, t2, t3, t4, hx]
      have hfd : WordR main (foldP qbody)
          (fun vs => vs = ofList ys :: .nil :: pM m sh sgn r p ++ rest)
          (fun _ out => LvlI m sh sgn r p u e rest ys.length out) (fun _ => BY) := by
        set L : ℕ := pSz m sh sgn r p + 15 * (m + 1) * (r + 1) * (p + 1) + 2 with hLs
        have hLsz : pSz m sh sgn r p + 15 * (m + 1) * (r + 1) * (p + 1) + 2 ≤ L := le_of_eq hLs.symm
        have hI0 : LvlI m sh sgn r p u e rest 0 (.nil :: pM m sh sgn r p ++ rest) :=
          ⟨[], rfl, rfl, by intro w hw; simp at hw, by intro b hb; omega⟩
        have hLsize : ∀ y ∈ ys, vsz y ≤ L := by
          intro y hy
          obtain ⟨x, hx, rfl⟩ := forall₂_exists hF hy
          have hx1 : vsz x ≤ 15 * (m + 1) * (r + 1) * (p + 1) := hLch x hx
          have hpv : vsz (prepVR m sh sgn r p) ≤ pSz m sh sgn r p := vsz_prepVR m sh sgn r p
          rw [MrgKit.vsz_cons', hLs]
          omega
        have hLb : L ≤ 60 * ((m + 1) * (r + 1) * (p + 1)) := by
          rw [hLs]
          have e : 15 * (m + 1) * (r + 1) * (p + 1) = 15 * ((m + 1) * (r + 1) * (p + 1)) := by ring
          have hmm : 2 ≤ 25 * ((m + 1) * (r + 1) * (p + 1)) := by
            have h := Nat.mul_le_mul_left 25 hM1
            simp only [mul_one] at h
            omega
          rw [e]
          linarith [hpszm, hmm]
        have hL4 : 4 ≤ L := by
          rw [hLs]
          have h1 : 3 ≤ m + 1 := by omega
          have h2 : 2 ≤ (r + 1) * (p + 1) := by
            rcases Nat.eq_zero_or_pos r with h | h
            · have hp1 : 1 ≤ p := by
                by_contra hc
                have hp0 : p = 0 := by omega
                rw [hp0] at hp; simp at hp; omega
              nlinarith
            · nlinarith
          have h3 : 6 ≤ (m + 1) * (r + 1) * (p + 1) := by nlinarith
          have h4 : 90 ≤ 15 * ((m + 1) * (r + 1) * (p + 1)) := by nlinarith
          linarith
        have hqstep : ∀ i acc, i < ys.length → LvlI m sh sgn r p u e rest i acc →
            WordR main qbody (fun vs => vs = ys.getD i .nil :: acc)
              (fun _ out => LvlI m sh sgn r p u e rest (i + 1) out)
              (fun _ => lvlBodyCost Kuc Kr Ksw Kdr Kcv Kb m r p L) := by
          intro i acc hi hI
          rw [hqbody]
          exact lvlFoldStep (hunc main) (hroll main) (hdr main) (hsw main) (hcons main) hblk
            m sh sgn r p u e t ws rest
            hm2 hmr hsgn hp hlen hind happ L hLsz ys hF i hi acc hI
        have hcL : (t / m) * L ≤ 120 * X := by
          have h3 := Nat.mul_le_mul_left (t / m) hLb
          have h4 : (t / m) * (60 * ((m + 1) * (r + 1) * (p + 1)))
              = 60 * ((t / m) * ((m + 1) * (r + 1) * (p + 1))) := by ring
          rw [h4] at h3
          have h5 : 60 * ((t / m) * ((m + 1) * (r + 1) * (p + 1))) ≤ 60 * (2 * X) :=
            Nat.mul_le_mul_left 60 hTM1
          have e : 60 * (2 * X) = 120 * X := by ring
          rw [e] at h5
          linarith [h3, h5]
        have hcL3 : (t / m) * (3 * L + 4) ≤ 500 * X := by
          have h3 : (t / m) * (3 * L + 4) ≤ (t / m) * (4 * L) :=
            Nat.mul_le_mul_left _ (by omega)
          have h4 : (t / m) * (4 * L) = 4 * ((t / m) * L) := by ring
          rw [h4] at h3
          have h5 : 4 * ((t / m) * L) ≤ 4 * (120 * X) := Nat.mul_le_mul_left 4 hcL
          have e : 4 * (120 * X) = 480 * X := by ring
          rw [e] at h5
          linarith [h3, h5]
        have hcL1 : (t / m) * (L + 1) ≤ 121 * X := by
          have h3 : (t / m) * (L + 1) = (t / m) * L + (t / m) := by ring
          rw [h3]
          linarith [hcL, htmX]
        have hD : ys.length
            * (lvlBodyCost Kuc Kr Ksw Kdr Kcv Kb m r p L + Kfl * (L + 1)) + Kfl ≤ BY := by
          have t1 : (t / m) * (6 * Kuc) ≤ (6 * Kuc) * X := by
            calc (t / m) * (6 * Kuc) ≤ X * (6 * Kuc) := Nat.mul_le_mul_right _ htmX
              _ = (6 * Kuc) * X := by ring
          have t2 : (t / m) * (5 * (Kr * 2 * (3 * L + 4))) ≤ (5000 * Kr) * X := by
            calc (t / m) * (5 * (Kr * 2 * (3 * L + 4)))
                = 10 * Kr * ((t / m) * (3 * L + 4)) := by ring
              _ ≤ 10 * Kr * (500 * X) := Nat.mul_le_mul_left _ hcL3
              _ = (5000 * Kr) * X := by ring
          have t3 : (t / m) * (Ksw * (3 * L + 4)) ≤ (500 * Ksw) * X := by
            calc (t / m) * (Ksw * (3 * L + 4)) = Ksw * ((t / m) * (3 * L + 4)) := by ring
              _ ≤ Ksw * (500 * X) := Nat.mul_le_mul_left _ hcL3
              _ = (500 * Ksw) * X := by ring
          have t4 : (t / m) * (Kdr * 2) ≤ (2 * Kdr) * X := by
            calc (t / m) * (Kdr * 2) = (Kdr * 2) * (t / m) := by ring
              _ ≤ (Kdr * 2) * X := Nat.mul_le_mul_left _ htmX
              _ = (2 * Kdr) * X := by ring
          have t5 : (t / m) * (Kr * 6 * (3 * L + 4)) ≤ (3000 * Kr) * X := by
            calc (t / m) * (Kr * 6 * (3 * L + 4)) = 6 * Kr * ((t / m) * (3 * L + 4)) := by ring
              _ ≤ 6 * Kr * (500 * X) := Nat.mul_le_mul_left _ hcL3
              _ = (3000 * Kr) * X := by ring
          have t6 : (t / m) * (Kb * m * (r + 1) * (p + 1)) ≤ Kb * X := by
            calc (t / m) * (Kb * m * (r + 1) * (p + 1))
                = Kb * ((t / m) * m * ((r + 1) * (p + 1))) := by ring
              _ ≤ Kb * (t * ((r + 1) * (p + 1))) := by
                  have h := Nat.div_mul_le_self t m
                  have h2 := Nat.mul_le_mul_right ((r + 1) * (p + 1)) h
                  exact Nat.mul_le_mul_left Kb h2
              _ = Kb * X := by rw [hX]; ring
          have t7 : (t / m) * Kb ≤ Kb * X := by
            calc (t / m) * Kb ≤ X * Kb := Nat.mul_le_mul_right Kb htmX
              _ = Kb * X := by ring
          have t8 : (t / m) * (5 * (Kr * 6 * (L + 1))) ≤ (3630 * Kr) * X := by
            calc (t / m) * (5 * (Kr * 6 * (L + 1))) = 30 * Kr * ((t / m) * (L + 1)) := by ring
              _ ≤ 30 * Kr * (121 * X) := Nat.mul_le_mul_left _ hcL1
              _ = (3630 * Kr) * X := by ring
          have t9 : (t / m) * (5 * (Kdr * (L + 1))) ≤ (605 * Kdr) * X := by
            calc (t / m) * (5 * (Kdr * (L + 1))) = 5 * Kdr * ((t / m) * (L + 1)) := by ring
              _ ≤ 5 * Kdr * (121 * X) := Nat.mul_le_mul_left _ hcL1
              _ = (605 * Kdr) * X := by ring
          have t10 : (t / m) * Kcv ≤ Kcv * X := by
            calc (t / m) * Kcv ≤ X * Kcv := Nat.mul_le_mul_right Kcv htmX
              _ = Kcv * X := by ring
          have t11 : (t / m) * (Kfl * (L + 1)) ≤ (121 * Kfl) * X := by
            calc (t / m) * (Kfl * (L + 1)) = Kfl * ((t / m) * (L + 1)) := by ring
              _ ≤ Kfl * (121 * X) := Nat.mul_le_mul_left _ hcL1
              _ = (121 * Kfl) * X := by ring
          have t12 : Kfl ≤ Kfl * X := le_mul_of_one_le _ hX1
          rw [hyclen, lvlBodyCost, hBY]
          have hcoef : 6 * Kuc + 5000 * Kr + 500 * Ksw + 2 * Kdr + 3000 * Kr + Kb + Kb
              + 3630 * Kr + 605 * Kdr + Kcv + 121 * Kfl + Kfl ≤ B := by rw [hB, hA]; omega
          have hx := Nat.mul_le_mul_right X hcoef
          linarith [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, hx]
        refine MrgKit.WordR_weaken
          (foldStep (hfold main) qbody ys (LvlI m sh sgn r p u e rest)
            (lvlBodyCost Kuc Kr Ksw Kdr Kcv Kb m r p L) L hLsize hqstep BY hD)
          (fun vs hvs => ?_) (fun _ _ _ h => h) (fun _ _ => le_rfl)
        exact ⟨(.nil :: pM m sh sgn r p) ++ rest, by rw [hvs, List.cons_append], hI0⟩
      have htd : ∀ (W : List (List (List (ℤ × ℤ)))), W.length = ys.length →
          (∀ w ∈ W, w.length = m ∧ (∀ z ∈ w, InDiscVec p r z)) →
          (∀ b < ys.length, ApproxSL p r m ((W.reverse).getD b []) (lvlN r m sgn (blkArr r u m b))
            (e + 1)) →
          WordR main (revP ;;; fltP)
            (fun vs => vs = ofList (W.map bVal) :: pM m sh sgn r p ++ rest)
            (fun _ out => Q out) (fun _ => BY) := by
        intro W hWlen hWall hWb
        have hWm : ∀ v ∈ W.reverse, v.length = m ∧ (∀ z ∈ v, InDiscVec p r z) :=
          fun v hv => hWall v (List.mem_reverse.mp hv)
        have hflat : ∀ w ∈ (W.reverse).flatten, InDiscVec p r w := by
          intro w hw
          obtain ⟨v, hv, hwv⟩ := List.mem_flatten.mp hw
          exact (hWm v hv).2 w hwv
        have hWrev : (W.reverse).length = t / m := by rw [List.length_reverse, hWlen, hyclen]
        have hV1 : vsz (ofList (W.map bVal)) ≤ 80 * X := by
          have hb1 : ∀ y ∈ W.map bVal, vsz y ≤ 15 * (m + 1) * (r + 1) * (p + 1) := by
            intro y hy
            obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hy
            exact vsz_ofList_cvecs_le_xlvlProg (m := m) (r := r) (p := p) (w := w)
              (hWall w hw).1 (hWall w hw).2
          have hbb := MrgKit.vsz_ofList_le_of_bound (W.map bVal)
            (15 * (m + 1) * (r + 1) * (p + 1)) (t / m) hb1
            (le_of_eq (by rw [List.length_map, hWlen, hyclen]))
          have h5 : (t / m) * (15 * (m + 1) * (r + 1) * (p + 1)) ≤ 40 * X := by
            calc (t / m) * (15 * (m + 1) * (r + 1) * (p + 1))
                = 15 * ((t / m) * ((m + 1) * (r + 1) * (p + 1))) := by ring
              _ ≤ 15 * (2 * X) := Nat.mul_le_mul_left 15 hTM1
              _ ≤ 40 * X := by linarith [hX1]
          linarith [hbb, h5, htmX, hX1]
        have hV2 : vsz (ofList ((W.reverse).map cvecs |>.map ofList)) ≤ 80 * X := by
          have hb1 : ∀ y ∈ (W.reverse).map cvecs |>.map ofList,
              vsz y ≤ 15 * (m + 1) * (r + 1) * (p + 1) := by
            intro y hy
            obtain ⟨u', hu', rfl⟩ := List.mem_map.mp hy
            obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hu'
            exact vsz_ofList_cvecs_le_xlvlProg (m := m) (r := r) (p := p) (w := w)
              (hWall w (List.mem_reverse.mp hw)).1 (hWall w (List.mem_reverse.mp hw)).2
          have hbb := MrgKit.vsz_ofList_le_of_bound ((W.reverse).map cvecs |>.map ofList)
            (15 * (m + 1) * (r + 1) * (p + 1)) (t / m) hb1
            (le_of_eq (by rw [List.length_map, List.length_map, List.length_reverse,
              hWlen, hyclen]))
          have h5 : (t / m) * (15 * (m + 1) * (r + 1) * (p + 1)) ≤ 40 * X := by
            calc (t / m) * (15 * (m + 1) * (r + 1) * (p + 1))
                = 15 * ((t / m) * ((m + 1) * (r + 1) * (p + 1))) := by ring
              _ ≤ 15 * (2 * X) := Nat.mul_le_mul_left 15 hTM1
              _ ≤ 40 * X := by linarith [hX1]
          linarith [hbb, h5, htmX, hX1]
        have happb : ApproxSL p r t ((W.reverse).flatten) (lvlN r m sgn u) (e + 1) := by
          refine approxSLOfBlocks (n := t / m) sgn (by omega) ?_ ?_ (fun v hv => (hWall v hv).1) ?_
          · rw [Nat.div_mul_cancel hdvd]
          · rw [hWlen, hyclen]
          · intro b hb
            have hb' : b < ys.length := by rw [hyclen]; exact hb
            have hbW : b < W.length := by rw [hWlen]; exact hb'
            have h := hWb b hb'
            have hr := rev_getD (W := W) b hbW
            rw [hr] at h
            rwa [hWlen, hyclen] at h
        have hD : Krev * (vsz (ofList (W.map bVal)) + 1)
            + Kflt * (vsz (ofList ((W.reverse).map cvecs |>.map ofList)) + 1) ≤ BY := by
          have hcoef : 81 * Krev + 81 * Kflt ≤ B := by rw [hB, hA]; omega
          have h3 := Nat.mul_le_mul_right X hcoef
          have t1 : Krev * (vsz (ofList (W.map bVal)) + 1) ≤ (81 * Krev) * X := by
            calc Krev * (vsz (ofList (W.map bVal)) + 1) ≤ Krev * (81 * X) :=
                Nat.mul_le_mul_left _ (by linarith [hV1, hX1])
              _ = (81 * Krev) * X := by ring
          have t2 : Kflt * (vsz (ofList ((W.reverse).map cvecs |>.map ofList)) + 1)
              ≤ (81 * Kflt) * X := by
            calc Kflt * (vsz (ofList ((W.reverse).map cvecs |>.map ofList)) + 1)
                ≤ Kflt * (81 * X) := Nat.mul_le_mul_left _ (by linarith [hV2, hX1])
              _ = (81 * Kflt) * X := by ring
          rw [hBY]
          linarith [t1, t2, h3]
        refine MrgKit.WordR_weaken
          (lvlTeardown (hrev main) (hflt main) m sh sgn r p W rest BY hD)
          (fun _ h => h) (fun _ out _ hQ' => ?_) (fun _ _ => le_rfl)
        rw [hQ]
        exact ⟨(W.reverse).flatten, hQ', happb.1, hflat, happb⟩
      have hft : WordR main (foldP qbody ;;; revP ;;; fltP)
          (fun vs => vs = ofList ys :: .nil :: pM m sh sgn r p ++ rest)
          (fun _ out => Q out) (fun _ => BY + BY) := by
        refine WordR_seq_gen hfd (fun mid hmid => ?_)
        obtain ⟨W, rfl, hWlen, hWall, hWb⟩ := hmid
        exact htd W hWlen hWall hWb
      refine WordR_seq_gen hcl' (fun mid hmid => ?_)
      rw [hmid]
      exact hft
    have hchain : WordR main (qpair ;;; qclean ;;; qtail)
        (fun vs => vs = ofList (chunkVals m ws) :: prepVR m sh sgn r p :: pM m sh sgn r p ++ rest)
        (fun _ out => Q out) (fun _ => BY + (BY + (BY + BY))) := by
      refine WordR_seq_gen hpair (fun mid hmid => ?_)
      obtain ⟨ys, rfl, hF⟩ := hmid
      exact hrest ys hF
    have hbig : WordR main (qsetup ;;; qpair ;;; qclean ;;; qtail)
        (fun vs => vs = ofList (cvecs ws) :: pM m sh sgn r p ++ rest)
        (fun _ out => Q out) (fun _ => BY + (BY + (BY + (BY + BY)))) := by
      refine WordR_seq_gen hs (fun mid hmid => ?_)
      rw [hmid]
      exact hchain
    have hpush2 : (ofList (cvecs ws) ≠ Val.nil →
        WordR main (qsetup ;;; qpair ;;; qclean ;;; qtail)
          (fun vs => vs = ofList (cvecs ws) :: pM m sh sgn r p ++ rest) (fun _ out => Q out)
          (fun _ => 5 * BY)) := fun _ =>
      MrgKit.WordR_weaken hbig (fun _ h => h) (fun _ _ _ h => h) (fun _ _ => by linarith)
    have hpush1 : (ofList (cvecs ws) = Val.nil → WordR main (pushP .nil)
        (fun vs => vs = pM m sh sgn r p ++ rest) (fun _ out => Q out) (fun _ => 0)) :=
      fun h => absurd h hvnil
    refine MrgKit.WordR_weaken
      (hiz main (pushP .nil) (qsetup ;;; qpair ;;; qclean ;;; qtail) (ofList (cvecs ws))
        (pM m sh sgn r p ++ rest) Q Q 0 (5 * BY) hpush1 hpush2) hpre ?_ ?_
    · intro vs out _ hq
      exact hpost out (hq.2 hvnil)
    · intro vs _
      have hmax : max 0 (5 * BY) = 5 * BY := max_eq_right (by linarith)
      rw [hmax]
      have h5 : 5 * BY ≤ Kfin * t * (r + 1) * (p + 1) := by
        have h6 := hBY5
        rw [hX] at h6
        have e : Kfin * (t * (r + 1) * (p + 1)) = Kfin * t * (r + 1) * (p + 1) := by ring
        rwa [e] at h6
      linarith [h5, hKiz]

end Work.SynFFT
