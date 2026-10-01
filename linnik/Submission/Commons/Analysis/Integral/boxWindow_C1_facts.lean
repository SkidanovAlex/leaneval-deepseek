import Mathlib
import Submission.Commons.Analysis.ExpLog.atanh_series_log_lower
import Submission.Commons.Analysis.Integral.L2log_lower_bound

namespace Commons.Analysis.Integral

/-- Numerator polynomial of the common-denominator form of `boxC1`. -/
noncomputable def boxNUM (β : ℝ) : ℝ := ((-1/4))*β^17 + (15)*β^16 + ((-843/4))*β^15 + (1217)*β^14 + ((-62601/32))*β^13 + (-15139)*β^12 + ((7321725/64))*β^11 + ((-25456001/64))*β^10 + ((887453903/1024))*β^9 + ((-319938387/256))*β^8 + ((288793965/256))*β^7 + ((-394855565/1024))*β^6 + ((-2396624041/4096))*β^5 + ((2525343541/2048))*β^4 + ((-656856209/512))*β^3 + ((219944965/256))*β^2 + ((-89493119/256))*β + (1047165/16)

/-- The (positive on `β < 2`) common denominator of `boxC1`. -/
noncomputable def boxDEN (β : ℝ) : ℝ :=
  ((3/2 - β)^2 + 1/4)^2 * ((1 + β)^2 + 1/4)^2 * (((2 - β)^2 + 1/4)^2) * (2 - β)^7

/-- The constant `C1` of the window estimate. -/
noncomputable def boxC1 (β : ℝ) : ℝ :=
  let A : ℝ := 3/2 - β
  let B : ℝ := 1 + β
  let C : ℝ := 2 - β
  let D : ℝ := C^2 - β^2
  let WTSt : ℝ := (13/5)*(A/((A^2+1/4)^2) + B/((B^2+1/4)^2))
      + D * (1/(2*((C^2+1/4)^2))) + D^2 * (1/(2*C^5)) + D^3 * (3/(8*C^7))
  WTSt + 1/(4*C^2)

lemma boxDEN_pos (β : ℝ) (h : β < 2) : (0:ℝ) < boxDEN β := by
  have h2 : (0:ℝ) < 2 - β := by linarith
  simp only [boxDEN]
  positivity

lemma boxC1_mul_den (β : ℝ) (h2 : (2:ℝ) - β ≠ 0) : boxC1 β * boxDEN β = boxNUM β := by
  have hA : (3/2-β)^2+1/4 ≠ 0 := by positivity
  have hB : (1+β)^2+1/4 ≠ 0 := by positivity
  have hC : (2-β)^2+1/4 ≠ 0 := by positivity
  simp only [boxC1, boxDEN, boxNUM]
  field_simp
  ring

lemma boxC1_le_three {β : ℝ} (h0 : (1:ℝ)/4 ≤ β) (h1 : β ≤ 1/2) : boxC1 β ≤ 3 := by
  have hu1 : (0:ℝ) ≤ β - 1/4 := by linarith
  have hu2 : (0:ℝ) ≤ 1/2 - β := by linarith
  have hDEN : (0:ℝ) < boxDEN β := boxDEN_pos β (by linarith)
  have hid : boxC1 β = boxNUM β / boxDEN β := by
    rw [eq_div_iff hDEN.ne']
    exact boxC1_mul_den β (by linarith)
  rw [hid, div_le_iff₀ hDEN]
  have hcert : (0:ℝ) ≤ 3 * boxDEN β - boxNUM β := by
    have hh : 3 * boxDEN β - boxNUM β = 535787754077649*((1/2)-β)^19 + 9257989999311870*(β-(1/4))^1*((1/2)-β)^18 + 75264144719356256*(β-(1/4))^2*((1/2)-β)^17 + 382625110287898128*(β-(1/4))^3*((1/2)-β)^16 + 1363458704517372832*(β-(1/4))^4*((1/2)-β)^15 + 3617354859274784960*(β-(1/4))^5*((1/2)-β)^14 + 7406629467417561344*(β-(1/4))^6*((1/2)-β)^13 + 11969376331001415680*(β-(1/4))^7*((1/2)-β)^12 + 15479246470841134336*(β-(1/4))^8*((1/2)-β)^11 + 16142254226102740480*(β-(1/4))^9*((1/2)-β)^10 + 13608698371225063424*(β-(1/4))^10*((1/2)-β)^9 + 9254447103284654080*(β-(1/4))^11*((1/2)-β)^8 + 5039784320121012224*(β-(1/4))^12*((1/2)-β)^7 + 2168565386984488960*(β-(1/4))^13*((1/2)-β)^6 + 721300771265052672*(β-(1/4))^14*((1/2)-β)^5 + 179050231236395008*(β-(1/4))^15*((1/2)-β)^4 + 31272009630482432*(β-(1/4))^16*((1/2)-β)^3 + 3440541800857600*(β-(1/4))^17*((1/2)-β)^2 + 182286129561600*(β-(1/4))^18*((1/2)-β)^1 + 553648128000*(β-(1/4))^19 := by
      simp only [boxDEN, boxNUM]
      ring
    rw [hh]
    positivity
  linarith

lemma RHS1_ge_six {β : ℝ} (h0 : (1:ℝ)/4 ≤ β) (h1 : β ≤ 1/2) :
    6 ≤ 3/(2*β) + 1/(1-β) + β/(1-β)^2 := by
  have hβ0 : (0:ℝ) < β := by linarith
  have hβ1 : (0:ℝ) < 1 - β := by linarith
  have hsplit : 3/(2*β) + 1/(1-β) + β/(1-β)^2
      = (3*(1-β)^2 + 2*β*(1-β) + 2*β^2)/(2*β*(1-β)^2) := by
    field_simp
  rw [hsplit, le_div_iff₀ (by positivity)]
  have hcert : (0:ℝ) ≤ 3*(1-β)^2 + 2*β*(1-β) + 2*β^2 - 6*(2*β*(1-β)^2) := by
    have hh : 3*(1-β)^2 + 2*β*(1-β) + 2*β^2 - 6*(2*β*(1-β)^2) = 32*((1/2)-β)^3 + 20*(β-(1/4))^1*((1/2)-β)^2 + 16*(β-(1/4))^2*((1/2)-β)^1 + 16*(β-(1/4))^3 := by
      ring
    rw [hh]
    have hu1 : (0:ℝ) ≤ β - 1/4 := by linarith
    have hu2 : (0:ℝ) ≤ 1/2 - β := by linarith
    positivity
  linarith

lemma twoC1_le_RHS2 {β : ℝ} (h0 : (1:ℝ)/2 ≤ β) (h1 : β ≤ 3/4) :
    2 * boxC1 β ≤ 2/(1-β) + 2/β - (1-β)/(2*β^2) := by
  have hβ0 : (0:ℝ) < β := by linarith
  have hβ1 : (0:ℝ) < 1 - β := by linarith
  have hDEN : (0:ℝ) < boxDEN β := boxDEN_pos β (by linarith)
  have hid : boxC1 β = boxNUM β / boxDEN β := by
    rw [eq_div_iff hDEN.ne']
    exact boxC1_mul_den β (by linarith)
  have hR : 2/(1-β) + 2/β - (1-β)/(2*β^2) = (6*β - 1 - β^2)/(2*β^2*(1-β)) := by
    field_simp
    ring
  have hD2 : (0:ℝ) < 2*β^2*(1-β) := by positivity
  rw [hid, hR, show 2 * (boxNUM β / boxDEN β) = (2*boxNUM β)/boxDEN β by ring]
  rw [div_le_iff₀ hDEN]
  rw [show ((6*β - 1 - β^2)/(2*β^2*(1-β))) * boxDEN β
        = ((6*β - 1 - β^2) * boxDEN β)/(2*β^2*(1-β)) by ring]
  rw [le_div_iff₀ hD2]
  have hcert : (0:ℝ) ≤ (6*β - 1 - β^2) * boxDEN β - (2*boxNUM β) * (2*β^2*(1-β)) := by
    have hh : (6*β - 1 - β^2) * boxDEN β - (2*boxNUM β) * (2*β^2*(1-β)) = 1151047041024000*((3/4)-β)^21 + 22838288528179200*(β-(1/2))^1*((3/4)-β)^20 + 215258910162944000*(β-(1/2))^2*((3/4)-β)^19 + 1282805441331462144*(β-(1/2))^3*((3/4)-β)^18 + 5426196112743596032*(β-(1/2))^4*((3/4)-β)^17 + 17334146694834028544*(β-(1/2))^5*((3/4)-β)^16 + 43433443070364876800*(β-(1/2))^6*((3/4)-β)^15 + 87495107698831130624*(β-(1/2))^7*((3/4)-β)^14 + 144065214450162130944*(β-(1/2))^8*((3/4)-β)^13 + 196017950555209756672*(β-(1/2))^9*((3/4)-β)^12 + 221875411623491522560*(β-(1/2))^10*((3/4)-β)^11 + 209607100476489984000*(β-(1/2))^11*((3/4)-β)^10 + 165282528644312187392*(β-(1/2))^12*((3/4)-β)^9 + 108454705886258352384*(β-(1/2))^13*((3/4)-β)^8 + 58836109841337386496*(β-(1/2))^14*((3/4)-β)^7 + 26107561266556629760*(β-(1/2))^15*((3/4)-β)^6 + 9322846956463191328*(β-(1/2))^16*((3/4)-β)^5 + 2614542291145123728*(β-(1/2))^17*((3/4)-β)^4 + 554643031056477904*(β-(1/2))^18*((3/4)-β)^3 + 83683199593411688*(β-(1/2))^19*((3/4)-β)^2 + 8002768858066606*(β-(1/2))^20*((3/4)-β)^1 + 364657215345319*(β-(1/2))^21 := by
      simp only [boxDEN, boxNUM]
      ring
    rw [hh]
    have hu1 : (0:ℝ) ≤ β - 1/2 := by linarith
    have hu2 : (0:ℝ) ≤ 3/4 - β := by linarith
    positivity
  linarith

lemma goalD_poly {β : ℝ} (h0 : (1:ℝ)/2 ≤ β) (h1 : β ≤ 3/4) :
    (2*β-1)*boxC1 β + 1 - 4*(2*β-1) - 4*(2*β-1)^3/3 - 4*(2*β-1)^5/5 - (1-β)^2/(4*β^2) ≤ 19/25 := by
  have hβ0 : (0:ℝ) < β := by linarith
  have hDEN : (0:ℝ) < boxDEN β := boxDEN_pos β (by linarith)
  have hid : boxC1 β = boxNUM β / boxDEN β := by
    rw [eq_div_iff hDEN.ne']
    exact boxC1_mul_den β (by linarith)
  have hpos : (0:ℝ) < (4*β^2) * boxDEN β := by positivity
  rw [← sub_nonneg]
  suffices hkey : (0:ℝ) ≤ ((4*β^2) * boxDEN β) *
      (19/25 - ((2*β-1)*boxC1 β + 1 - 4*(2*β-1) - 4*(2*β-1)^3/3 - 4*(2*β-1)^5/5 - (1-β)^2/(4*β^2))) by
    exact nonneg_of_mul_nonneg_right hkey hpos
  rw [hid]
  have hh : ((4*β^2) * boxDEN β) *
      (19/25 - ((2*β-1)*(boxNUM β/boxDEN β) + 1 - 4*(2*β-1) - 4*(2*β-1)^3/3 - 4*(2*β-1)^5/5 - (1-β)^2/(4*β^2))) = 46965467381760000*((3/4)-β)^26 + 1180237685587968000*(β-(1/2))^1*((3/4)-β)^25 + 15186921036290457600*(β-(1/2))^2*((3/4)-β)^24 + 129970223056148234240*(β-(1/2))^3*((3/4)-β)^23 + 812817433200892575744*(β-(1/2))^4*((3/4)-β)^22 + (19479584782229528641536/5)*(β-(1/2))^5*((3/4)-β)^21 + (368696767065903914287104/25)*(β-(1/2))^6*((3/4)-β)^20 + (225230497713658680836096/5)*(β-(1/2))^7*((3/4)-β)^19 + (2820674061760842759667712/25)*(β-(1/2))^8*((3/4)-β)^18 + (5865664299168071296221184/25)*(β-(1/2))^9*((3/4)-β)^17 + (6133926093302701922189312/15)*(β-(1/2))^10*((3/4)-β)^16 + (3007674815433815000875008/5)*(β-(1/2))^11*((3/4)-β)^15 + (11257350337239845663408128/15)*(β-(1/2))^12*((3/4)-β)^14 + (11948192039471853465239552/15)*(β-(1/2))^13*((3/4)-β)^13 + (3600614249474765150748672/5)*(β-(1/2))^14*((3/4)-β)^12 + (8314153602642290427035648/15)*(β-(1/2))^15*((3/4)-β)^11 + (27179630526737633509081088/75)*(β-(1/2))^16*((3/4)-β)^10 + (3006143166986883333013504/15)*(β-(1/2))^17*((3/4)-β)^9 + (2328131769619856025714688/25)*(β-(1/2))^18*((3/4)-β)^8 + (2701261670790875306221568/75)*(β-(1/2))^19*((3/4)-β)^7 + (171610846597509747132416/15)*(β-(1/2))^20*((3/4)-β)^6 + (8788961821942593037312/3)*(β-(1/2))^21*((3/4)-β)^5 + (1766596273950312512512/3)*(β-(1/2))^22*((3/4)-β)^4 + (267846801528536504320/3)*(β-(1/2))^23*((3/4)-β)^3 + (28731266159664068608/3)*(β-(1/2))^24*((3/4)-β)^2 + 645913133834369024*(β-(1/2))^25*((3/4)-β)^1 + 20519912296013312*(β-(1/2))^26 := by
    have hA : (3/2-β)^2+1/4 ≠ 0 := by positivity
    have hB : (1+β)^2+1/4 ≠ 0 := by positivity
    have hC : (2-β)^2+1/4 ≠ 0 := by positivity
    have hb0 : β ≠ 0 := hβ0.ne'
    have h2b : (2:ℝ) - β ≠ 0 := by linarith
    simp only [boxDEN, boxNUM]
    field_simp
    ring
  rw [hh]
  have hu1 : (0:ℝ) ≤ β - 1/2 := by linarith
  have hu2 : (0:ℝ) ≤ 3/4 - β := by linarith
  positivity

lemma log_ratio_upper {β : ℝ} (hβ0 : 0 < β) (h1 : β ≤ 1/2) :
    Real.log (β/(1-β)) ≤ -2*(1-2*β) := by
  have hβ1 : (0:ℝ) < 1 - β := by linarith
  have hy1 : (1:ℝ) ≤ (1-β)/β := by rw [le_div_iff₀ hβ0]; linarith
  have h := two_mul_sub_div_le_log hy1
  have hlog : Real.log ((1-β)/β) = - Real.log (β/(1-β)) := by
    rw [← Real.log_inv]
    congr 1
    field_simp
  have hsimp : 2*(((1-β)/β) - 1)/(((1-β)/β) + 1) = 2*(1-2*β) := by
    field_simp
    ring
  rw [hlog, hsimp] at h
  linarith

lemma log_ratio_lower {β : ℝ} (h0 : 1/2 ≤ β) (hβ1 : β < 1) :
    4*(2*β-1) + 4*(2*β-1)^3/3 + 4*(2*β-1)^5/5 ≤ 2*Real.log (β/(1-β)) := by
  rcases lt_or_eq_of_le h0 with hlt | heq
  · have hu0 : (0:ℝ) < 2*β-1 := by linarith
    have hu1 : 2*β-1 < 1 := by linarith
    have h := Commons.Analysis.ExpLog.atanh_series_log_lower hu0 hu1 2
    have hsum : (∑ k ∈ Finset.range 3, (2*β-1)^(2*k+1)/(2*k+1 : ℝ))
        = (2*β-1) + (2*β-1)^3/3 + (2*β-1)^5/5 := by
      norm_num [Finset.sum_range_succ]
    rw [hsum] at h
    have hratio : (1 + (2*β-1))/(1 - (2*β-1)) = β/(1-β) := by
      have hb0 : β ≠ 0 := by linarith
      have h1b : (1:ℝ) - β ≠ 0 := by linarith
      have h2b : 1 - (2*β-1) ≠ 0 := by linarith
      field_simp
      ring
    rw [hratio] at h
    linarith
  · rw [← heq]
    norm_num

lemma F2b_bound {β : ℝ} (h0 : (1:ℝ)/4 ≤ β) (h1 : β ≤ 1/2) :
    (1-2*β)*boxC1 β + Real.log (β/(1-β)) + β/(1-β) - Real.log (2*β) + Real.log β - 1/4
      ≤ 3/4 - Real.log 2 + 1/100 := by
  have hβ0 : (0:ℝ) < β := by linarith
  have hβ1 : β < 1 := by linarith
  have hC1 := boxC1_le_three h0 h1
  have hlog := log_ratio_upper hβ0 h1
  have hnonneg : (0:ℝ) ≤ 1 - 2*β := by linarith
  have hmon : (1-2*β)*boxC1 β ≤ (1-2*β)*3 := mul_le_mul_of_nonneg_left hC1 hnonneg
  have h1mβ : (0:ℝ) < 1 - β := by linarith
  have halg : β/(1-β) ≤ 2*β := by
    rw [div_le_iff₀ h1mβ]; nlinarith
  have hlog2 : Real.log (2*β) = Real.log 2 + Real.log β := by
    rw [Real.log_mul (by norm_num) hβ0.ne']
  rw [hlog2]
  linarith

lemma F2c_bound {β : ℝ} (h0 : (1:ℝ)/2 ≤ β) (h1 : β ≤ 3/4) :
    (2*β-1)*boxC1 β + Real.log ((1-β)/β) + 1 - Real.log (2*β) + Real.log (1-β) - (1-β)^2/(4*β^2)
      ≤ 3/4 - Real.log 2 + 1/100 := by
  have hβ0 : (0:ℝ) < β := by linarith
  have hβ1 : β < 1 := by linarith
  have h1mβ : (0:ℝ) < 1 - β := by linarith
  have hD := goalD_poly h0 h1
  have hlow := log_ratio_lower (by linarith : (1:ℝ)/2 ≤ β) hβ1
  have hlog_inv : Real.log ((1-β)/β) = - Real.log (β/(1-β)) := by
    rw [← Real.log_inv]
    congr 1
    field_simp
  have hcore : (2*β-1)*boxC1 β + 1 + 2*Real.log ((1-β)/β) - (1-β)^2/(4*β^2) ≤ 19/25 := by
    rw [hlog_inv]
    linarith
  have hlog1 : Real.log (2*β) = Real.log 2 + Real.log β := by
    rw [Real.log_mul (by norm_num) hβ0.ne']
  have hlog2 : Real.log ((1-β)/β) = Real.log (1-β) - Real.log β := by
    rw [Real.log_div h1mβ.ne' hβ0.ne']
  have hgoal_eq : (2*β-1)*boxC1 β + Real.log ((1-β)/β) + 1 - Real.log (2*β) + Real.log (1-β) - (1-β)^2/(4*β^2)
      = ((2*β-1)*boxC1 β + 1 + 2*Real.log ((1-β)/β) - (1-β)^2/(4*β^2)) - Real.log 2 := by
    rw [hlog1, hlog2]; ring
  rw [hgoal_eq]
  linarith

theorem boxWindow_C1_facts {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
  (let A : ℝ := 3/2 - β;
   let B : ℝ := 1 + β;
   let C : ℝ := 2 - β;
   let D : ℝ := C^2 - β^2;
   let WTSt : ℝ := (13/5)*(A/((A^2+1/4)^2) + B/((B^2+1/4)^2))
      + D * (1/(2*((C^2+1/4)^2))) + D^2 * (1/(2*C^5)) + D^3 * (3/(8*C^7));
   let C1 : ℝ := WTSt + 1/(4*C^2);
   let F2b : ℝ := (1-2*β)*C1 + Real.log (β/(1-β)) + β/(1-β) - Real.log (2*β) + Real.log β - 1/4;
   let F2c : ℝ := (2*β-1)*C1 + Real.log ((1-β)/β) + 1 - Real.log (2*β) + Real.log (1-β) - (1-β)^2/(4*β^2);
   (1/4 ≤ β → β ≤ 1/2 → 2*C1 ≤ 3/(2*β) + 1/(1-β) + β/(1-β)^2) ∧
   (1/2 ≤ β → β ≤ 3/4 → 2*C1 ≤ 2/(1-β) + 2/β - (1-β)/(2*β^2)) ∧
   (1/4 ≤ β → β ≤ 1/2 → F2b ≤ 3/4 - Real.log 2 + 1/100) ∧
   (1/2 ≤ β → β ≤ 3/4 → F2c ≤ 3/4 - Real.log 2 + 1/100)) := by
  change (1/4 ≤ β → β ≤ 1/2 → 2*boxC1 β ≤ 3/(2*β) + 1/(1-β) + β/(1-β)^2) ∧
    (1/2 ≤ β → β ≤ 3/4 → 2*boxC1 β ≤ 2/(1-β) + 2/β - (1-β)/(2*β^2)) ∧
    (1/4 ≤ β → β ≤ 1/2 → (1-2*β)*boxC1 β + Real.log (β/(1-β)) + β/(1-β) - Real.log (2*β) + Real.log β - 1/4 ≤ 3/4 - Real.log 2 + 1/100) ∧
    (1/2 ≤ β → β ≤ 3/4 → (2*β-1)*boxC1 β + Real.log ((1-β)/β) + 1 - Real.log (2*β) + Real.log (1-β) - (1-β)^2/(4*β^2) ≤ 3/4 - Real.log 2 + 1/100)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h0 h1
    have hC1 := boxC1_le_three h0 h1
    have hR := RHS1_ge_six h0 h1
    linarith
  · intro h0 h1; exact twoC1_le_RHS2 h0 h1
  · intro h0 h1; exact F2b_bound h0 h1
  · intro h0 h1; exact F2c_bound h0 h1

end Commons.Analysis.Integral
