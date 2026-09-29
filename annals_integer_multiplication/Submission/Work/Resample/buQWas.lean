import Mathlib
import Submission.Work.Resample.buQWdefs
import Submission.Work.Resample.buQWkey
import Submission.Work.Resample.buQWsel
import Submission.Work.Resample.buQWscal
import Submission.Work.Resample.buQWrnd2
import Submission.Work.Resample.buQWbr3
import Submission.Work.Resample.buQWwireK
import Submission.Work.Resample.buQWrowsum
import Submission.Work.Resample.buQWwtacc
import Submission.Work.Resample.buQWwdb
import Submission.Work.Resample.egW_decay

/-!
# `Work.Resample.buQWas`: the assembly of the one-dimensional `B̃` word

The requested statement of `Work.Resample.buQW`.  The program together with the wiring of the three
stage words `buQWsel`, `buQWrnd2`, `buQWscal` is `Work.Resample.buQWwireK`; here we supply those
three stage words, discharge the two analytic hypotheses (`hrow` from `buQWrowsum` + `buQWwtacc` +
`egW_decay`, `hwd` from `buQWwdb`) and convert the list-level postcondition `w = buPhiL p α s t u`
into the `Fin s`-level one (`buQWbridge`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH

/-! ## two injectivity facts for the vector encoding -/

private lemma ofList_inj' : Function.Injective (HvdH.ofList : List HvdH.Val → HvdH.Val) := by
  intro l
  induction l with
  | nil =>
      intro m h
      cases m with
      | nil => rfl
      | cons b bs => simp [HvdH.ofList] at h
  | cons a as ih =>
      intro m h
      cases m with
      | nil => simp [HvdH.ofList] at h
      | cons b bs =>
          have h' : a = b ∧ HvdH.ofList as = HvdH.ofList bs := by
            simpa [HvdH.ofList] using h
          obtain ⟨h1, h2⟩ := h'
          rw [h1, ih h2]

private lemma map_cfxVal_inj {u v : List (ℤ × ℤ)} (h : u.map HvdH.cfxVal = v.map HvdH.cfxVal) :
    u = v := by
  induction u generalizing v with
  | nil => cases v <;> simp_all
  | cons a as ih =>
      cases v with
      | nil => simp_all
      | cons b bs =>
          obtain ⟨h1, h2⟩ := List.cons.inj h
          have hab : a = b := by
            have hh : a.1 = b.1 ∧ a.2 = b.2 := by
              simpa [HvdH.cfxVal] using h1
            exact Prod.ext hh.1 hh.2
          rw [hab, ih h2]

/-! ## the assembly -/

theorem buQWas (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib) (FL : HvdH.FxLib) :
    ∃ (q : HvdH.Cmd) (K : ℕ),
    ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t) (htp : t < 2 ^ p)
      (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
      (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1)
      (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm → K * p < N →
    HvdH.WordR main q
      (fun vs => ∃ (u : List (ℤ × ℤ)) (rest : List HvdH.Val),
        vs = HvdH.ofList (u.map HvdH.cfxVal) :: Work.Resample.buTabList p α s t (by omega) hcop.symm ++ rest ∧
        u.length = t ∧ (∀ z ∈ u, HvdH.inDisc p z))
      (fun vs out => ∃ (u : List (ℤ × ℤ)) (rest : List HvdH.Val) (w : List (ℤ × ℤ)),
        vs = HvdH.ofList (u.map HvdH.cfxVal) :: Work.Resample.buTabList p α s t (by omega) hcop.symm ++ rest ∧
        out = HvdH.cvecVal w :: Work.Resample.buTabList p α s t (by omega) hcop.symm ++ rest ∧
        w.length = s ∧ (∀ z ∈ w, HvdH.inDisc p z) ∧
        (∀ k : Fin s, w.getD k (0, 0) =
          Work.Resample.buPhi (Work.Resample.buWt p α s t) (Work.Resample.buWd p α s t) p α s t
            (by omega) hcop.symm (fun j => u.getD j (0, 0)) k))
      (fun _ => Work.Resample.egCostShape K p α t Cm) := by
  obtain ⟨selW, Ksel, hsel⟩ := buQWsel KL IL LL FL
  obtain ⟨rndW, Krnd, hrnd⟩ := buQWrnd2 KL IL LL FL
  obtain ⟨sclW, Kscl, hscl⟩ := buQWscal KL IL LL FL
  obtain ⟨q, Kw, hwire⟩ := buQWwireK KL IL LL FL selW rndW sclW Ksel Krnd Kscl hsel hrnd hscl
  refine ⟨q, Kw, ?_⟩
  intro p α s t hs hst hcop htp hα hp hαp hθ main N Cm hm hmb hKN
  have hrow : ∀ ℓ : ℤ, ∑ h ∈ egHset (egM p α), |(buWt p α s t ℓ h : ℝ)| ≤
      (2 : ℝ) ^ p / 2 + 8 * (egM p α : ℝ) := by
    intro ℓ
    exact (buQWrowsum p α s t hs hst hα hp ℓ
      (fun h hh => buQWwtacc p α s t hs hst hα hp ℓ h hh)
      (fun h hh => by simpa [egWBnd] using (egW_decay s t α p hs hst hα hαp hθ ℓ).1 h hh)).1
  have hwd : ∀ ℓ : ℤ, 8 * (buWd p α s t ℓ).natAbs ≤ 3 * 2 ^ p :=
    fun ℓ => buQWwdb p α s t hs hst hα hp ℓ
  have hW := hwire p α s t hs hst hcop htp hα hp hαp hθ hrow hwd main N Cm hm hmb hKN
  refine KL.conseq main q _ _ _ _ _ _ hW ?_ ?_ ?_
  · intro vs h
    obtain ⟨u, rest, hvs, hulen, hdisc⟩ := h
    exact ⟨u, rest, hvs, hulen, fun z hz => (inDisc_iff_buIn p z).mp (hdisc z hz)⟩
  · intro vs out hpv hq
    obtain ⟨u, rest, hvs, hulen, hdisc⟩ := hpv
    obtain ⟨u', rest', w, hvs', hout, hw, hwlen, hwinV⟩ := hq
    have hcons : HvdH.ofList (u'.map HvdH.cfxVal) ::
          Work.Resample.buTabList p α s t (by omega) hcop.symm ++ rest'
        = HvdH.ofList (u.map HvdH.cfxVal) ::
          Work.Resample.buTabList p α s t (by omega) hcop.symm ++ rest := by
      rw [← hvs', hvs]
    obtain ⟨hhead, htail⟩ := List.cons.inj hcons
    have hu : u' = u := map_cfxVal_inj (ofList_inj' hhead)
    have hrst : rest' = rest := (List.append_inj htail rfl).2
    rw [hu] at hw
    rw [hrst] at hout
    have hbr := buQWbr3 p α s t (by omega) hcop.symm u hulen
    refine ⟨u, rest, w, hvs, hout, ?_, ?_, ?_⟩
    · rw [hw]; exact hbr.1
    · intro z hz
      exact (inDisc_iff_buIn p z).mpr (hwinV z hz)
    · intro k
      rw [hw]
      exact hbr.2 k
  · intro vs _
    exact le_rfl

end Work.Resample
