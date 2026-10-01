import Mathlib
import Submission.Commons.Analysis.Integral.boxWindow_C1_facts

namespace Commons.Analysis.Integral

noncomputable section

/-- The derivative-helper `2/u + (1+β-u)/(1-u)^2 - u/(2β^2)`. -/
def boxBr (β u : ℝ) : ℝ := 2/u + (1+β-u)/(1-u)^2 - u/(2*β^2)

/-- The `F2f` expression of the statement, as a function of `u` for fixed `β`. -/
def boxPhi (β : ℝ) (u : ℝ) : ℝ :=
  (1 - 2*u)*boxC1 β + (Real.log u - Real.log (1-u)) + β/(1-u) - Real.log (2*β)
    + Real.log u - u^2/(4*β^2)

/-! ### The two bounds on `boxBr` -/

lemma boxBr_ge_six {β u : ℝ} (hu : 1/4 ≤ u) (hβu : u ≤ β) (hβ : β ≤ 1/2) :
    6 ≤ boxBr β u := by
  have hu0 : (0:ℝ) < u := by linarith
  have h1u : (0:ℝ) < 1-u := by linarith
  have hβ0 : (0:ℝ) < β := by linarith
  have h1 : (0:ℝ) ≤ u - 1/4 := by linarith
  have h2 : (0:ℝ) ≤ 1/2 - u := by linarith
  have hsplit : boxBr β u - (3/(2*u) + 1/(1-u)^2)
      = (β-u)*(1/(1-u)^2 + (β+u)/(2*u*β^2)) := by
    unfold boxBr; field_simp; ring
  have hnn : 0 ≤ boxBr β u - (3/(2*u) + 1/(1-u)^2) := by
    rw [hsplit]
    exact mul_nonneg (by linarith) (by positivity)
  have heq : 3/(2*u) + 1/(1-u)^2 - 6
      = (32*((1/2)-u)^3 + 20*(u-1/4)*((1/2)-u)^2 + 16*(u-1/4)^2*((1/2)-u)
          + 16*(u-1/4)^3)/(2*u*(1-u)^2) := by
    field_simp; ring
  have h6 : 0 ≤ 3/(2*u) + 1/(1-u)^2 - 6 := by
    rw [heq]; positivity
  linarith

lemma boxBr_ge_lin {β u : ℝ} (hβ : 1/2 ≤ β) (hβ' : β ≤ 3/4) (hu : 1/4 ≤ u)
    (huβ : u ≤ 1-β) : 8*β + 2 ≤ boxBr β u := by
  have hu0 : (0:ℝ) < u := by linarith
  have h1u : (0:ℝ) < 1-u := by linarith
  have hβ0 : (0:ℝ) < β := by linarith
  have h1 : (0:ℝ) ≤ u - 1/4 := by linarith
  have h2 : (0:ℝ) ≤ β - 1/2 := by linarith
  have h3 : (0:ℝ) ≤ 1 - β - u := by linarith
  have hid : boxBr β u - (8*β+2)
      = (4*(1-u)^2*β^2 + 2*u*β^2*(1+β-u) - u^2*(1-u)^2 - (8*β+2)*(2*u*(1-u)^2*β^2))
          / (2*u*(1-u)^2*β^2) := by
    unfold boxBr; field_simp; ring
  have hnum : 0 ≤ 4*(1-u)^2*β^2 + 2*u*β^2*(1+β-u) - u^2*(1-u)^2
      - (8*β+2)*(2*u*(1-u)^2*β^2) := by
    have hh : 4*(1-u)^2*β^2 + 2*u*β^2*(1+β-u) - u^2*(1-u)^2
        - (8*β+2)*(2*u*(1-u)^2*β^2)
        = (1072)*(u-1/4)^0*(β-1/2)^0*(1-β-u)^6 + (7200)*(u-1/4)^0*(β-1/2)^1*(1-β-u)^5 + (19776)*(u-1/4)^0*(β-1/2)^2*(1-β-u)^4 + (28432)*(u-1/4)^0*(β-1/2)^3*(1-β-u)^3 + (22560)*(u-1/4)^0*(β-1/2)^4*(1-β-u)^2 + (9360)*(u-1/4)^0*(β-1/2)^5*(1-β-u)^1 + (1584)*(u-1/4)^0*(β-1/2)^6*(1-β-u)^0 + (4640)*(u-1/4)^1*(β-1/2)^0*(1-β-u)^5 + (25376)*(u-1/4)^1*(β-1/2)^1*(1-β-u)^4 + (54064)*(u-1/4)^1*(β-1/2)^2*(1-β-u)^3 + (55984)*(u-1/4)^1*(β-1/2)^3*(1-β-u)^2 + (28080)*(u-1/4)^1*(β-1/2)^4*(1-β-u)^1 + (5424)*(u-1/4)^1*(β-1/2)^5*(1-β-u)^0 + (8240)*(u-1/4)^2*(β-1/2)^0*(1-β-u)^4 + (35392)*(u-1/4)^2*(β-1/2)^1*(1-β-u)^3 + (55072)*(u-1/4)^2*(β-1/2)^2*(1-β-u)^2 + (36640)*(u-1/4)^2*(β-1/2)^3*(1-β-u)^1 + (8720)*(u-1/4)^2*(β-1/2)^4*(1-β-u)^0 + (7872)*(u-1/4)^3*(β-1/2)^0*(1-β-u)^3 + (25280)*(u-1/4)^3*(β-1/2)^1*(1-β-u)^2 + (26048)*(u-1/4)^3*(β-1/2)^2*(1-β-u)^1 + (8576)*(u-1/4)^3*(β-1/2)^3*(1-β-u)^0 + (4480)*(u-1/4)^4*(β-1/2)^0*(1-β-u)^2 + (9856)*(u-1/4)^4*(β-1/2)^1*(1-β-u)^1 + (5248)*(u-1/4)^4*(β-1/2)^2*(1-β-u)^0 + (1536)*(u-1/4)^5*(β-1/2)^0*(1-β-u)^1 + (1792)*(u-1/4)^5*(β-1/2)^1*(1-β-u)^0 + (256)*(u-1/4)^6*(β-1/2)^0*(1-β-u)^0 := by
      ring
    rw [hh]; positivity
  have := div_nonneg hnum (by positivity : (0:ℝ) ≤ 2*u*(1-u)^2*β^2)
  linarith [hid]

/-! ### The two upper bounds on `boxC1` -/

lemma two_boxC1_le_six {β : ℝ} (hβ : 1/4 ≤ β) (hβ' : β ≤ 1/2) : 2*boxC1 β ≤ 6 := by
  have h := boxC1_le_three hβ hβ'
  linarith

lemma two_boxC1_le_lin {β : ℝ} (hβ : 1/2 ≤ β) (hβ' : β ≤ 3/4) : 2*boxC1 β ≤ 8*β+2 := by
  have hβ0 : (0:ℝ) < β := by linarith
  have hDEN : (0:ℝ) < boxDEN β := boxDEN_pos β (by linarith)
  have hid : boxC1 β = boxNUM β / boxDEN β := by
    rw [eq_div_iff hDEN.ne']; exact boxC1_mul_den β (by linarith)
  have hcert : 0 ≤ (8*β+2)*boxDEN β - 2*boxNUM β := by
    have hh : (8*β+2)*boxDEN β - 2*boxNUM β
        = (4429185024000)*(β-1/2)^0*(3/4-β)^20 + (1007684891443200)*(β-1/2)^1*(3/4-β)^19 + (15826959938355200)*(β-1/2)^2*(3/4-β)^18 + (120422555549958144)*(β-1/2)^3*(3/4-β)^17 + (578875288417468416)*(β-1/2)^4*(3/4-β)^16 + (1962898007875649536)*(β-1/2)^5*(3/4-β)^15 + (4980809382985465856)*(β-1/2)^6*(3/4-β)^14 + (9799769161197682688)*(β-1/2)^7*(3/4-β)^13 + (15289288011611471872)*(β-1/2)^8*(3/4-β)^12 + (19184267157920202752)*(β-1/2)^9*(3/4-β)^11 + (19518469518803472384)*(β-1/2)^10*(3/4-β)^10 + (16158046427164080128)*(β-1/2)^11*(3/4-β)^9 + (10874964372561911808)*(β-1/2)^12*(3/4-β)^8 + (5920306404084842496)*(β-1/2)^13*(3/4-β)^7 + (2580965294294098432)*(β-1/2)^14*(3/4-β)^6 + (886454904403841792)*(β-1/2)^15*(3/4-β)^5 + (233886164863393408)*(β-1/2)^16*(3/4-β)^4 + (45573475498414400)*(β-1/2)^17*(3/4-β)^3 + (6145266091648592)*(β-1/2)^18*(3/4-β)^2 + (508074637404568)*(β-1/2)^19*(3/4-β)^1 + (19164471209728)*(β-1/2)^20*(3/4-β)^0 := by
      simp only [boxDEN, boxNUM]; ring
    rw [hh]
    have h1 : (0:ℝ) ≤ β - 1/2 := by linarith
    have h2 : (0:ℝ) ≤ 3/4 - β := by linarith
    positivity
  rw [hid, show 2*(boxNUM β/boxDEN β) = (2*boxNUM β)/boxDEN β by ring]
  rw [div_le_iff₀ hDEN]
  linarith



/-! ### Derivative of `boxPhi` in the second variable -/

lemma hasDerivAt_boxPhi {β u : ℝ} (hβ0 : β ≠ 0) (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (boxPhi β) (boxBr β u - 2*boxC1 β) u := by
  have h1u : (0:ℝ) < 1 - u := by linarith
  have hsub : HasDerivAt (fun u : ℝ => 1 - u) (-1) u := (hasDerivAt_id u).const_sub (1:ℝ)
  have hp1 : HasDerivAt (fun u : ℝ => (1 - 2*u)*boxC1 β) (-2*boxC1 β) u := by
    have hlin : HasDerivAt (fun u : ℝ => 1 - 2*u) (-2:ℝ) u := by
      have h := ((hasDerivAt_id u).const_mul (2:ℝ)).const_sub (1:ℝ)
      simpa using h
    have c := hlin.mul_const (boxC1 β)
    convert c using 1 <;> try ring
  have hp2 : HasDerivAt (fun u : ℝ => Real.log u - Real.log (1-u)) (1/u + 1/(1-u)) u := by
    have a : HasDerivAt Real.log u⁻¹ u := Real.hasDerivAt_log hu0.ne'
    have b : HasDerivAt (fun u : ℝ => Real.log (1-u)) ((-1)/(1-u)) u := by
      simpa using hsub.log (by linarith : (1:ℝ) - u ≠ 0)
    have c := a.sub b
    convert c using 1 <;> try rfl
    rw [inv_eq_one_div, neg_div, sub_neg_eq_add]
  have hp3 : HasDerivAt (fun u : ℝ => β/(1-u)) (β/(1-u)^2) u := by
    have c := (hasDerivAt_const (x:=u) (c:=β)).div hsub (by linarith : (1:ℝ)-u ≠ 0)
    convert c using 1 <;> try rfl
    field_simp
    ring
  have hp4 : HasDerivAt (fun _ : ℝ => Real.log (2*β)) 0 u := hasDerivAt_const u (Real.log (2*β))
  have hp5 : HasDerivAt Real.log (1/u) u := by
    simpa [one_div] using (Real.hasDerivAt_log hu0.ne')
  have hp6 : HasDerivAt (fun u : ℝ => u^2/(4*β^2)) (u/(2*β^2)) u := by
    have hp : HasDerivAt (fun u : ℝ => u^2) (2*u) u := by
      simpa using (hasDerivAt_pow 2 u)
    have c := hp.div_const (4*β^2)
    convert c using 1 <;> try rfl
    field_simp
    ring
  have hcomb := ((((hp1.add hp2).add hp3).sub hp4).add hp5).sub hp6
  convert hcomb using 1 <;> try rfl
  unfold boxBr
  field_simp
  ring

/-! ### Monotonicity of `boxPhi` in `u` -/

lemma boxPhi_mono_left {β : ℝ} (hβ : 1/4 ≤ β) (hβ' : β ≤ 1/2) :
    MonotoneOn (boxPhi β) (Set.Icc (1/4) β) := by
  have hβ0 : (0:ℝ) < β := by linarith
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    (f' := fun x => boxBr β x - 2*boxC1 β) (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
  · exact ((hasDerivAt_boxPhi hβ0.ne' (by linarith [hx.1]) (by linarith [hx.2, hβ'])).continuousAt).continuousWithinAt
  · rw [interior_Icc] at hx
    exact (hasDerivAt_boxPhi hβ0.ne' (by linarith [hx.1]) (by linarith [hx.2, hβ'])).hasDerivWithinAt
  · rw [interior_Icc] at hx
    have h1 := boxBr_ge_six (le_of_lt hx.1) (le_of_lt hx.2) hβ'
    have h2 := two_boxC1_le_six hβ hβ'
    linarith

lemma boxPhi_mono_right {β : ℝ} (hβ : 1/2 ≤ β) (hβ' : β ≤ 3/4) :
    MonotoneOn (boxPhi β) (Set.Icc (1/4) (1-β)) := by
  have hβ0 : (0:ℝ) < β := by linarith
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    (f' := fun x => boxBr β x - 2*boxC1 β) (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
  · exact ((hasDerivAt_boxPhi hβ0.ne' (by linarith [hx.1]) (by linarith [hx.2])).continuousAt).continuousWithinAt
  · rw [interior_Icc] at hx
    exact (hasDerivAt_boxPhi hβ0.ne' (by linarith [hx.1]) (by linarith [hx.2])).hasDerivWithinAt
  · rw [interior_Icc] at hx
    have h1 := boxBr_ge_lin hβ hβ' (le_of_lt hx.1) (le_of_lt hx.2)
    have h2 := two_boxC1_le_lin hβ hβ'
    linarith

/-! ### The two endpoint values -/

lemma boxPhi_at_self {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    boxPhi β β = (1-2*β)*boxC1 β + Real.log (β/(1-β)) + β/(1-β) - Real.log (2*β)
      + Real.log β - 1/4 := by
  have h1β : (1:ℝ) - β ≠ 0 := by linarith
  have hsq : β^2/(4*β^2) = (1:ℝ)/4 := by
    rw [div_eq_iff (by positivity)]; ring
  unfold boxPhi
  rw [Real.log_div hβ0.ne' h1β, hsq]

lemma boxPhi_at_one_sub {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    boxPhi β (1-β) = (2*β-1)*boxC1 β + Real.log ((1-β)/β) + 1 - Real.log (2*β)
      + Real.log (1-β) - (1-β)^2/(4*β^2) := by
  have h1β : (1:ℝ) - β ≠ 0 := by linarith
  have h1b : (1:ℝ) - (1 - β) = β := by ring
  have hbb : β/β = (1:ℝ) := by field_simp
  unfold boxPhi
  rw [Real.log_div h1β hβ0.ne', h1b, hbb]
  ring

/-! ### The main bound -/

theorem boxWindow_F2f_bound {β u : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hu : 1/4 ≤ u)
    (hβu : u ≤ β) (hu2 : u ≤ 1-β) :
  (let A : ℝ := 3/2 - β;
   let B : ℝ := 1 + β;
   let C : ℝ := 2 - β;
   let D : ℝ := C^2 - β^2;
   let WTSt : ℝ := (13/5)*(A/((A^2+1/4)^2) + B/((B^2+1/4)^2))
      + D * (1/(2*((C^2+1/4)^2))) + D^2 * (1/(2*C^5)) + D^3 * (3/(8*C^7));
   let C1 : ℝ := WTSt + 1/(4*C^2);
   (1-2*u)*C1 + Real.log (u/(1-u)) + β/(1-u) - Real.log (2*β) + Real.log u - u^2/(4*β^2)
     ≤ 3/4 - Real.log 2 + 1/100) := by
  have hu0 : (0:ℝ) < u := by linarith
  have h1u : (0:ℝ) < 1 - u := by linarith
  have hβge : 1/4 ≤ β := le_trans hu hβu
  have hβle : β ≤ 3/4 := by linarith
  change (1-2*u)*boxC1 β + Real.log (u/(1-u)) + β/(1-u) - Real.log (2*β) + Real.log u
      - u^2/(4*β^2) ≤ 3/4 - Real.log 2 + 1/100
  rw [Real.log_div hu0.ne' h1u.ne']
  change boxPhi β u ≤ 3/4 - Real.log 2 + 1/100
  rcases le_total β (1/2) with hle | hge
  · have hmono := boxPhi_mono_left hβge hle
    have h1 : boxPhi β u ≤ boxPhi β β :=
      hmono ⟨hu, hβu⟩ ⟨hβge, le_refl β⟩ hβu
    have h2 : boxPhi β β ≤ 3/4 - Real.log 2 + 1/100 := by
      rw [boxPhi_at_self hβ0 hβ1]
      exact F2b_bound hβge hle
    linarith
  · have hmono := boxPhi_mono_right hge hβle
    have h1 : boxPhi β u ≤ boxPhi β (1-β) :=
      hmono ⟨hu, hu2⟩ ⟨by linarith, le_refl (1-β)⟩ hu2
    have h2 : boxPhi β (1-β) ≤ 3/4 - Real.log 2 + 1/100 := by
      rw [boxPhi_at_one_sub hβ0 hβ1]
      exact F2c_bound hge hβle
    linarith

end

end Commons.Analysis.Integral
